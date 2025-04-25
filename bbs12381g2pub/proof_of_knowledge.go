/*
Copyright SecureKey Technologies Inc. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0
*/

package bbs12381g2pub

import (
	"fmt"

	//	"math/rand"

	"time"

	ml "github.com/IBM/mathlib"
)

// PoKOfSignature is Proof of Knowledge of a Signature that is used by the prover to construct PoKOfSignatureProof.
type PoKOfSignature struct {
	aPrime *ml.G1
	aBar   *ml.G1
	d      *ml.G1

	u      *ml.G1
	uBar   *ml.G1
	ComCid *ml.G1
	dCid   *ml.G1

	pokVC1   *ProverCommittedG1 //存储了bases和blindingFactor 以及com
	secrets1 []*ml.Zr

	pokVC2   *ProverCommittedG1
	secrets2 []*ml.Zr

	pokVC3   *ProverCommittedG1
	secrets3 []*ml.Zr

	pokVC4   *ProverCommittedG1
	secrets4 []*ml.Zr

	pokVC5   *ProverCommittedG1
	secrets5 []*ml.Zr

	pokVC6   *ProverCommittedG1
	secrets6 []*ml.Zr

	revealedMessages map[int]*SignatureMessage
}

// NewPoKOfSignature creates a new PoKOfSignature.
func NewPoKOfSignature(signature *Signature, messages []*SignatureMessage, revealedIndexes []int,
	pubKey *PublicKeyWithGenerators) (*PoKOfSignature, error) {
	err := signature.Verify(messages, pubKey)
	if err != nil {
		return nil, fmt.Errorf("verify input signature: %w", err)
	}

	r1, r2 := createRandSignatureFr(), createRandSignatureFr()
	b := computeB(signature.S, signature.CID, messages, pubKey)
	aPrime := signature.A.Mul(frToRepr(r1))

	aBarDenom := aPrime.Mul(frToRepr(signature.E))

	aBar := b.Mul(frToRepr(r1))
	aBar.Sub(aBarDenom)

	r2D := r2.Copy()
	r2D.Neg()

	commitmentBasesCount := 2
	cb := newCommitmentBuilder(commitmentBasesCount)
	cb.add(b, r1)
	cb.add(pubKey.h0, r2D)

	d := cb.build()
	r3 := r1.Copy()
	r3.InvModP(curve.GroupOrder)

	sPrime := r2.Mul(r3)
	sPrime.Neg()
	sPrime = sPrime.Plus(signature.S)
	//+++++++++++++++++++++++++++++++++++++++
	currentDate := time.Now().Format("20060102")
	hashT := frFromOKM([]byte(currentDate))

	//	i := int64(rand.Intn(5))
	pr := curve.GenG1.Copy()
	r4, r5 := createRandSignatureFr(), createRandSignatureFr()

	J := curve.NewZrFromInt(1)
	e := signature.E.Copy()
	sn := e.Plus(hashT)
	sn = sn.Plus(J)
	sn.Neg()
	u := pubKey.phi.Mul(sn)
	dCid := pubKey.h02.Mul(sn)
	dCid.Add(pr.Mul(frToRepr(r5)))

	uBar := u.Mul(signature.E)

	ComCid := pubKey.h02.Mul(frToRepr(signature.CID))

	ComCid.Add(pr.Mul(frToRepr(r4)))
	//---------------------------------------

	pokVC1, secrets1 := newVC1Signature(aPrime, pubKey.h0, signature.E, r2)

	revealedMessages := make(map[int]*SignatureMessage, len(revealedIndexes))

	if len(messages) < len(revealedIndexes) {
		return nil, fmt.Errorf("invalid size: %d revealed indexes is larger than %d messages", len(revealedIndexes),
			len(messages))
	}

	for _, ind := range revealedIndexes {
		revealedMessages[ind] = messages[ind]
	}

	//Add cid
	pokVC2, secrets2, pokVC3, secrets3 := newVC2Signature(d, r3, r4, signature.CID, signature.E, pubKey, sPrime, messages, revealedMessages)
	pokVC4, secrets4, pokVC5, secrets5, pokVC6, secrets6 := newVC3Signature(u, pubKey.phi, pubKey.h02, r5, signature.E)
	return &PoKOfSignature{
		aPrime: aPrime,
		aBar:   aBar,
		d:      d,
		u:      u,
		uBar:   uBar,
		ComCid: ComCid,

		pokVC1:   pokVC1, //com & bases & blindingFactors
		secrets1: secrets1,
		pokVC2:   pokVC2,
		secrets2: secrets2,

		pokVC3:   pokVC3,
		secrets3: secrets3,
		pokVC4:   pokVC4,
		secrets4: secrets4,
		pokVC5:   pokVC5,
		secrets5: secrets5,
		pokVC6:   pokVC6,
		secrets6: secrets6,

		revealedMessages: revealedMessages,
	}, nil
}

// pokVC1=A'^{r} h0^{r}
// secrets1:[-e,r2]
func newVC1Signature(aPrime *ml.G1, h0 *ml.G1,
	e, r2 *ml.Zr) (*ProverCommittedG1, []*ml.Zr) {
	committing1 := NewProverCommittingG1()
	secrets1 := make([]*ml.Zr, 2)

	committing1.Commit(aPrime)

	sigE := e.Copy()
	sigE.Neg()
	secrets1[0] = sigE

	committing1.Commit(h0)

	secrets1[1] = r2
	pokVC1 := committing1.Finish()

	return pokVC1, secrets1
}

// pokVC2=d^{r} h0^{r} Πhi^{r}
// secrets2:[-r3,s',{mi}]
func newVC2Signature(d *ml.G1, r3, r4, e, cid *ml.Zr, pubKey *PublicKeyWithGenerators, sPrime *ml.Zr,
	messages []*SignatureMessage, revealedMessages map[int]*SignatureMessage) (*ProverCommittedG1, []*ml.Zr, *ProverCommittedG1, []*ml.Zr) {
	messagesCount := len(messages)
	committing2 := NewProverCommittingG1()

	baseSecretsCount := 3
	secrets2 := make([]*ml.Zr, 0, baseSecretsCount+messagesCount)
	secrets3 := make([]*ml.Zr, 0, 1)

	committing2.CommitCid(pubKey.h02, e)
	secrets2 = append(secrets2, cid)

	committing3 := committing2.CommittingCopy() //Com_cid = h02^{cid}*g1^{r4}
	secrets3 = append(secrets3, cid)
	g1 := curve.GenG1.Copy()
	committing3.Commit(g1)
	secrets3 = append(secrets3, r4)
	pokVC3 := committing3.Finish()

	committing2.Commit(d)

	r3D := r3.Copy()
	r3D.Neg()

	secrets2 = append(secrets2, r3D)

	committing2.Commit(pubKey.h0)

	secrets2 = append(secrets2, sPrime)

	for i := 0; i < messagesCount; i++ {
		if _, ok := revealedMessages[i]; ok {
			continue
		}

		committing2.Commit(pubKey.h[i])

		sourceFR := messages[i].FR
		hiddenFRCopy := sourceFR.Copy()

		secrets2 = append(secrets2, hiddenFRCopy)
	}

	pokVC2 := committing2.Finish()

	return pokVC2, secrets2, pokVC3, secrets3
}

// ++++++++++++++++++++++++++
func newVC3Signature(u, phi, h02 *ml.G1, r5, e *ml.Zr) (*ProverCommittedG1, []*ml.Zr, *ProverCommittedG1, []*ml.Zr, *ProverCommittedG1, []*ml.Zr) {
	committing4 := NewProverCommittingG1() //u=\phi^{(e+J+H_1(T))^{-1}}
	committing5 := NewProverCommittingG1() //d_{cid}=\tilde{h}^{(e+J+H_1(T))^{-1}}g_1^{r_5}\}(n_{2})
	committing6 := NewProverCommittingG1() //\bar{u}=u^{-e}

	secrets4 := make([]*ml.Zr, 1)
	committing4.Commit(phi)

	currentDate := time.Now().Format("20060102")
	hashT := frFromOKM([]byte(currentDate))
	J := curve.NewZrFromInt(1)
	sn := e.Plus(hashT)
	sn = sn.Plus(J)
	sn.Neg()
	secrets4 = append(secrets4, sn)
	pokVC4 := committing4.Finish()

	committing5 = committing4.CommittingCopyReplaceLastBase(h02)
	secrets5 := make([]*ml.Zr, 2)
	secrets5 = append(secrets5, sn)
	pr := curve.GenG1.Copy()
	committing5.Commit(pr)
	secrets5 = append(secrets4, r5)
	pokVC5 := committing5.Finish()

	secrets6 := make([]*ml.Zr, 1)
	committing6.Commit(u)
	negE := e.Copy()
	negE.Neg()
	secrets6 = append(secrets6, negE)
	pokVC6 := committing6.Finish()

	return pokVC4, secrets4, pokVC5, secrets5, pokVC6, secrets6
}

//--------------------------

// ToBytes converts PoKOfSignature to bytes.
func (pos *PoKOfSignature) ToBytes() []byte {
	challengeBytes := pos.aBar.Bytes()
	challengeBytes = append(challengeBytes, pos.pokVC1.ToBytes()...)
	challengeBytes = append(challengeBytes, pos.pokVC2.ToBytes()...)

	return challengeBytes
}

// GenerateProof generates PoKOfSignatureProof proof from PoKOfSignature signature.
func (pos *PoKOfSignature) GenerateProof(challengeHash *ml.Zr) *PoKOfSignatureProof {
	return &PoKOfSignatureProof{
		aPrime:   pos.aPrime,
		aBar:     pos.aBar,
		d:        pos.d,
		proofVC1: pos.pokVC1.GenerateProof(challengeHash, pos.secrets1),
		proofVC2: pos.pokVC2.GenerateProof(challengeHash, pos.secrets2),
	}
}

// ProverCommittedG1 helps to generate a ProofG1.
type ProverCommittedG1 struct {
	bases           []*ml.G1
	blindingFactors []*ml.Zr
	commitment      *ml.G1
}

// ToBytes converts ProverCommittedG1 to bytes.
func (g *ProverCommittedG1) ToBytes() []byte {
	bytes := make([]byte, 0)

	for _, base := range g.bases {
		bytes = append(bytes, base.Bytes()...)
	}

	return append(bytes, g.commitment.Bytes()...)
}

// GenerateProof generates proof ProofG1 for all secrets.
func (g *ProverCommittedG1) GenerateProof(challenge *ml.Zr, secrets []*ml.Zr) *ProofG1 {
	responses := make([]*ml.Zr, len(g.bases))

	for i := range g.blindingFactors {
		c := challenge.Mul(secrets[i])

		s := g.blindingFactors[i].Minus(c)
		responses[i] = s
	}

	return &ProofG1{
		commitment: g.commitment,
		responses:  responses,
	}
}

// ProverCommittingG1 is a proof of knowledge of messages in a vector commitment.
type ProverCommittingG1 struct {
	bases           []*ml.G1
	blindingFactors []*ml.Zr
}

// NewProverCommittingG1 creates a new ProverCommittingG1.
func NewProverCommittingG1() *ProverCommittingG1 {
	return &ProverCommittingG1{
		bases:           make([]*ml.G1, 0),
		blindingFactors: make([]*ml.Zr, 0),
	}
}

func (pc *ProverCommittingG1) CommittingCopy() *ProverCommittingG1 {
	// Copy bases
	basesCopy := make([]*ml.G1, len(pc.bases))
	copy(basesCopy, pc.bases)

	// Copy blindingFactors
	blindingFactorsCopy := make([]*ml.Zr, len(pc.blindingFactors))
	copy(blindingFactorsCopy, pc.blindingFactors)

	return &ProverCommittingG1{
		bases:           basesCopy,
		blindingFactors: blindingFactorsCopy,
	}
}

// Commit append a base point and randomly generated blinding factor.
func (pc *ProverCommittingG1) Commit(base *ml.G1) {
	pc.bases = append(pc.bases, base)
	r := createRandSignatureFr()
	pc.blindingFactors = append(pc.blindingFactors, r)
}

// +++++++++++++++++++++++0425+++commit cid++++++++++++++++
// 不不不这个i不应该在这里，而是生成证明前就要指定
// DeriveProof--> NewPoKOfSignature--> newVC2Signature--> Commit Cid
func (pc *ProverCommittingG1) CommitCid(base *ml.G1, e *ml.Zr) {
	pc.bases = append(pc.bases, base)
	currentDate := time.Now().Format("20060102")
	hashT := frFromOKM([]byte(currentDate))

	//	i := int64(rand.Intn(5))
	J := curve.NewZrFromInt(1)
	r := e.Plus(hashT)
	r = r.Plus(J)
	r.Neg()
	pc.blindingFactors = append(pc.blindingFactors, r)
}

//———————————————————————0425————commit cid————————————————

func (pc *ProverCommittingG1) CommittingCopyReplaceLastBase(base *ml.G1) *ProverCommittingG1 {
	// Copy bases
	basesCopy := make([]*ml.G1, len(pc.bases))
	copy(basesCopy, pc.bases)

	// Replace the last base if there are bases
	if len(basesCopy) > 0 {
		basesCopy[len(basesCopy)-1] = base
	}

	// Copy blindingFactors
	blindingFactorsCopy := make([]*ml.Zr, len(pc.blindingFactors))
	copy(blindingFactorsCopy, pc.blindingFactors)

	return &ProverCommittingG1{
		bases:           basesCopy,
		blindingFactors: blindingFactorsCopy,
	}
}

// Finish helps to generate ProverCommittedG1 after commitment of all base points.
func (pc *ProverCommittingG1) Finish() *ProverCommittedG1 {
	commitment := sumOfG1Products(pc.bases, pc.blindingFactors)

	return &ProverCommittedG1{
		bases:           pc.bases,
		blindingFactors: pc.blindingFactors,
		commitment:      commitment,
	}
}
