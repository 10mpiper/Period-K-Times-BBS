/*
Copyright SecureKey Technologies Inc. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0
*/

package bbs12381g2pub

import (
	"encoding/binary"
	"errors"
	"fmt"
	"time"

	ml "github.com/IBM/mathlib"
)

// PoKOfSignatureProof defines BLS signature proof.
// It is the actual proof that is sent from prover to verifier.
type PoKOfSignatureProof struct {
	aPrime *ml.G1
	aBar   *ml.G1
	d      *ml.G1
	u      *ml.G1
	uBar   *ml.G1
	ComCid *ml.G1

	proofVC1 *ProofG1
	proofVC2 *ProofG1
	proofVC3 *ProofG1
	proofVC4 *ProofG1
	proofVC5 *ProofG1
	proofVC6 *ProofG1
}

// GetBytesForChallenge creates bytes for proof challenge.
// 好好好，修改过后应该是 PokSignature.ToBytes()||nonce
func (sp *PoKOfSignatureProof) GetBytesForChallenge(revealedMessages map[int]*SignatureMessage,
	pubKey *PublicKeyWithGenerators) []byte {
	hiddenCount := pubKey.messagesCount - len(revealedMessages)

	bytesLen := (17 + hiddenCount) * g1UncompressedSize //nolint:gomnd
	bytes := make([]byte, 0, bytesLen)

	bytes = append(bytes, sp.aBar.Bytes()...)
	bytes = append(bytes, sp.aPrime.Bytes()...)
	bytes = append(bytes, pubKey.h0.Bytes()...)
	bytes = append(bytes, sp.proofVC1.commitment.Bytes()...)
	bytes = append(bytes, sp.d.Bytes()...)
	bytes = append(bytes, pubKey.h0.Bytes()...)

	for i := range pubKey.h {
		if _, ok := revealedMessages[i]; !ok {
			bytes = append(bytes, pubKey.h[i].Bytes()...)
		}
	}

	bytes = append(bytes, sp.proofVC2.commitment.Bytes()...)
	bytes = append(bytes, pubKey.h0.Bytes()...)
	g1 := curve.GenG1.Copy()
	bytes = append(bytes, g1.Bytes()...)
	bytes = append(bytes, sp.proofVC3.commitment.Bytes()...)

	bytes = append(bytes, pubKey.phi.Bytes()...)
	bytes = append(bytes, sp.proofVC4.commitment.Bytes()...)

	bytes = append(bytes, pubKey.h02.Bytes()...)
	bytes = append(bytes, g1.Bytes()...)
	bytes = append(bytes, sp.proofVC5.commitment.Bytes()...)

	bytes = append(bytes, sp.u.Bytes()...)
	bytes = append(bytes, sp.proofVC6.commitment.Bytes()...)

	return bytes
}

// Verify verifies PoKOfSignatureProof.
func (sp *PoKOfSignatureProof) Verify(challenge *ml.Zr, pubKey *PublicKeyWithGenerators,
	revealedMessages map[int]*SignatureMessage, messages []*SignatureMessage) error {
	aBar := sp.aBar.Copy()
	aBar.Neg()

	ok := compareTwoPairings(sp.aPrime, pubKey.w, aBar, curve.GenG2)
	if !ok {
		return errors.New("bad signature")
	}

	uBar := sp.uBar.Copy()
	u := sp.u.Copy()
	uBar.Add(pubKey.phi)

	currentDate := time.Now().Format("20060102")
	hashT := frFromOKM([]byte(currentDate))
	J := curve.NewZrFromInt(1)
	// J := 1 + H(T)
	J.Plus(hashT)

	g2 := curve.GenG2.Copy()
	g2J := curve.GenG2.Copy()
	g2J.Mul(J)

	ok1 := compareTwoPairings(uBar, g2, u, g2J)
	if !ok1 {
		return errors.New("bad signature")
	}

	err1 := sp.verifyVC1Proof(challenge, pubKey)
	if err1 != nil {
		return err1
	}

	err2 := sp.verifyVC2Proof(challenge, pubKey, revealedMessages, messages)
	if err2 != nil {
		return err2
	}

	err3 := sp.verifyVC3Proof(challenge, pubKey)
	if err3 != nil {
		return err3
	}

	err4 := sp.verifyVC4Proof(challenge, pubKey)
	if err4 != nil {
		return err4
	}

	err5 := sp.verifyVC5Proof(challenge, pubKey)
	if err5 != nil {
		return err5
	}

	return sp.verifyVC6Proof(challenge)

}

func (sp *PoKOfSignatureProof) verifyVC1Proof(challenge *ml.Zr, pubKey *PublicKeyWithGenerators) error {
	basesVC1 := []*ml.G1{sp.aPrime, pubKey.h0}
	aBarD := sp.aBar.Copy()
	aBarD.Sub(sp.d)

	err := sp.proofVC1.Verify(basesVC1, aBarD, challenge)
	if err != nil {
		return errors.New("bad signature")
	}

	return nil
}

// 计算statement，bases
func (sp *PoKOfSignatureProof) verifyVC2Proof(challenge *ml.Zr, pubKey *PublicKeyWithGenerators,
	revealedMessages map[int]*SignatureMessage, messages []*SignatureMessage) error {
	revealedMessagesCount := len(revealedMessages)

	basesVC2 := make([]*ml.G1, 0, 3+pubKey.messagesCount-revealedMessagesCount) //这里的2改为3
	basesVC2 = append(basesVC2, sp.d, pubKey.h0, pubKey.h02)                    //Add pubKey.h02

	//这四行是干啥的
	basesDisclosed := make([]*ml.G1, 0, 1+revealedMessagesCount)
	exponents := make([]*ml.Zr, 0, 1+revealedMessagesCount)

	basesDisclosed = append(basesDisclosed, curve.GenG1)
	exponents = append(exponents, curve.NewZrFromInt(1)) //expose g1 firstly

	revealedMessagesInd := 0

	for i := range pubKey.h {
		if _, ok := revealedMessages[i]; ok {
			basesDisclosed = append(basesDisclosed, pubKey.h[i])
			exponents = append(exponents, messages[revealedMessagesInd].FR)
			revealedMessagesInd++
		} else {
			basesVC2 = append(basesVC2, pubKey.h[i])
		}
	}

	// TODO: expose 0
	pr := curve.GenG1.Copy()
	pr.Sub(curve.GenG1)

	for i := 0; i < len(basesDisclosed); i++ {
		b := basesDisclosed[i]
		s := exponents[i]

		g := b.Mul(frToRepr(s))
		pr.Add(g)
	}

	pr.Neg() //statement=g1^{-1} Πhi^{-mi}

	err := sp.proofVC2.Verify(basesVC2, pr, challenge)
	if err != nil {
		return errors.New("bad signature")
	}

	return nil
}

func (sp *PoKOfSignatureProof) verifyVC3Proof(challenge *ml.Zr, pubKey *PublicKeyWithGenerators) error {
	g1 := curve.GenG1.Copy()
	basesVC3 := []*ml.G1{pubKey.h02, g1}

	err := sp.proofVC3.Verify(basesVC3, sp.ComCid, challenge)
	if err != nil {
		return errors.New("bad signature")
	}

	return nil
}

func (sp *PoKOfSignatureProof) verifyVC4Proof(challenge *ml.Zr, pubKey *PublicKeyWithGenerators) error {
	basesVC4 := []*ml.G1{pubKey.phi}

	err := sp.proofVC3.Verify(basesVC4, sp.u, challenge)
	if err != nil {
		return errors.New("bad signature")
	}

	return nil
}

func (sp *PoKOfSignatureProof) verifyVC5Proof(challenge *ml.Zr, pubKey *PublicKeyWithGenerators) error {
	g1 := curve.GenG1.Copy()
	basesVC5 := []*ml.G1{pubKey.h02, g1}

	err := sp.proofVC3.Verify(basesVC5, sp.proofVC3.commitment, challenge) //注意这里的dCid
	if err != nil {
		return errors.New("bad signature")
	}

	return nil
}

func (sp *PoKOfSignatureProof) verifyVC6Proof(challenge *ml.Zr) error {
	basesVC6 := []*ml.G1{sp.u}

	err := sp.proofVC3.Verify(basesVC6, sp.uBar, challenge)
	if err != nil {
		return errors.New("bad signature")
	}

	return nil
}

// ToBytes converts PoKOfSignatureProof to bytes.
func (sp *PoKOfSignatureProof) ToBytes() []byte {
	bytes := make([]byte, 0)

	bytes = append(bytes, sp.aPrime.Compressed()...)
	bytes = append(bytes, sp.aBar.Compressed()...)
	bytes = append(bytes, sp.d.Compressed()...)
	bytes = append(bytes, sp.u.Compressed()...)
	bytes = append(bytes, sp.uBar.Compressed()...)
	bytes = append(bytes, sp.ComCid.Compressed()...)

	proof1Bytes := sp.proofVC1.ToBytes()
	lenBytes1 := make([]byte, 4)
	binary.BigEndian.PutUint32(lenBytes1, uint32(len(proof1Bytes)))
	bytes = append(bytes, lenBytes1...)
	bytes = append(bytes, proof1Bytes...)

	proof2Bytes := sp.proofVC2.ToBytes()
	lenBytes2 := make([]byte, 4)
	binary.BigEndian.PutUint32(lenBytes2, uint32(len(proof2Bytes)))
	bytes = append(bytes, lenBytes2...)
	bytes = append(bytes, proof2Bytes...)

	proof3Bytes := sp.proofVC3.ToBytes()
	lenBytes3 := make([]byte, 4)
	binary.BigEndian.PutUint32(lenBytes3, uint32(len(proof3Bytes)))
	bytes = append(bytes, lenBytes3...)
	bytes = append(bytes, proof3Bytes...)

	proof4Bytes := sp.proofVC4.ToBytes()
	lenBytes4 := make([]byte, 4)
	binary.BigEndian.PutUint32(lenBytes4, uint32(len(proof4Bytes)))
	bytes = append(bytes, lenBytes4...)
	bytes = append(bytes, proof4Bytes...)

	proof5Bytes := sp.proofVC5.ToBytes()
	lenBytes5 := make([]byte, 4)
	binary.BigEndian.PutUint32(lenBytes5, uint32(len(proof5Bytes)))
	bytes = append(bytes, lenBytes5...)
	bytes = append(bytes, proof5Bytes...)

	bytes = append(bytes, sp.proofVC6.ToBytes()...)

	return bytes
}

// ProofG1 is a proof of knowledge of a signature and hidden messages.
type ProofG1 struct {
	commitment *ml.G1
	responses  []*ml.Zr
}

// NewProofG1 creates a new ProofG1.
func NewProofG1(commitment *ml.G1, responses []*ml.Zr) *ProofG1 {
	return &ProofG1{
		commitment: commitment,
		responses:  responses,
	}
}

// Verify verifies the ProofG1.
func (pg1 *ProofG1) Verify(bases []*ml.G1, commitment *ml.G1, challenge *ml.Zr) error {
	contribution := pg1.getChallengeContribution(bases, commitment, challenge)
	contribution.Sub(pg1.commitment)

	if !contribution.IsInfinity() {
		return errors.New("contribution is not zero")
	}

	return nil
}

func (pg1 *ProofG1) getChallengeContribution(bases []*ml.G1, commitment *ml.G1,
	challenge *ml.Zr) *ml.G1 {
	points := append(bases, commitment)
	scalars := append(pg1.responses, challenge)

	return sumOfG1Products(points, scalars)
}

// ToBytes converts ProofG1 to bytes.
func (pg1 *ProofG1) ToBytes() []byte {
	bytes := make([]byte, 0)

	commitmentBytes := pg1.commitment.Compressed()
	bytes = append(bytes, commitmentBytes...)

	lenBytes := make([]byte, 4)
	binary.BigEndian.PutUint32(lenBytes, uint32(len(pg1.responses)))
	bytes = append(bytes, lenBytes...)

	for i := range pg1.responses {
		responseBytes := frToRepr(pg1.responses[i]).Bytes()
		bytes = append(bytes, responseBytes...)
	}

	return bytes
}

// ParseSignatureProof parses a signature proof.
func ParseSignatureProof(sigProofBytes []byte) (*PoKOfSignatureProof, error) {
	if len(sigProofBytes) < g1CompressedSize*6 {
		return nil, errors.New("invalid size of signature proof")
	}

	g1Points := make([]*ml.G1, 6)
	offset := 0

	for i := range g1Points {
		g1Point, err := curve.NewG1FromCompressed(sigProofBytes[offset : offset+g1CompressedSize])
		if err != nil {
			return nil, fmt.Errorf("parse G1 point: %w", err)
		}

		g1Points[i] = g1Point
		offset += g1CompressedSize
	}

	proof1BytesLen1 := int(uint32FromBytes(sigProofBytes[offset : offset+4]))
	offset += 4

	proofVc1, err := ParseProofG1(sigProofBytes[offset : offset+proof1BytesLen1])
	if err != nil {
		return nil, fmt.Errorf("parse G1 proof: %w", err)
	}

	offset += proof1BytesLen1
	proof1BytesLen2 := int(uint32FromBytes(sigProofBytes[offset : offset+4]))
	offset += 4
	proofVc2, err := ParseProofG1(sigProofBytes[offset : offset+proof1BytesLen2])
	if err != nil {
		return nil, fmt.Errorf("parse G1 proof: %w", err)
	}

	offset += proof1BytesLen2
	proof1BytesLen3 := int(uint32FromBytes(sigProofBytes[offset : offset+4]))
	offset += 4
	proofVc3, err := ParseProofG1(sigProofBytes[offset : offset+proof1BytesLen3])
	if err != nil {
		return nil, fmt.Errorf("parse G1 proof: %w", err)
	}

	offset += proof1BytesLen3
	proof1BytesLen4 := int(uint32FromBytes(sigProofBytes[offset : offset+4]))
	offset += 4
	proofVc4, err := ParseProofG1(sigProofBytes[offset : offset+proof1BytesLen4])
	if err != nil {
		return nil, fmt.Errorf("parse G1 proof: %w", err)
	}

	offset += proof1BytesLen4
	proof1BytesLen5 := int(uint32FromBytes(sigProofBytes[offset : offset+4]))
	offset += 4
	proofVc5, err := ParseProofG1(sigProofBytes[offset : offset+proof1BytesLen5])
	if err != nil {
		return nil, fmt.Errorf("parse G1 proof: %w", err)
	}

	offset += proof1BytesLen5

	proofVc6, err := ParseProofG1(sigProofBytes[offset:])
	if err != nil {
		return nil, fmt.Errorf("parse G1 proof: %w", err)
	}

	return &PoKOfSignatureProof{
		aPrime: g1Points[0],
		aBar:   g1Points[1],
		d:      g1Points[2],
		u:      g1Points[3],
		uBar:   g1Points[4],
		ComCid: g1Points[5],

		proofVC1: proofVc1,
		proofVC2: proofVc2,
		proofVC3: proofVc3,
		proofVC4: proofVc4,
		proofVC5: proofVc5,
		proofVC6: proofVc6,
	}, nil
}

// ParseProofG1 parses ProofG1 from bytes.
func ParseProofG1(bytes []byte) (*ProofG1, error) {
	if len(bytes) < g1CompressedSize+4 {
		return nil, errors.New("invalid size of G1 signature proof")
	}

	offset := 0

	commitment, err := curve.NewG1FromCompressed(bytes[:g1CompressedSize])
	if err != nil {
		return nil, fmt.Errorf("parse G1 point: %w", err)
	}

	offset += g1CompressedSize
	length := int(uint32FromBytes(bytes[offset : offset+4]))
	offset += 4

	if len(bytes) < g1CompressedSize+4+length*frCompressedSize {
		return nil, errors.New("invalid size of G1 signature proof")
	}

	responses := make([]*ml.Zr, length)
	for i := 0; i < length; i++ {
		responses[i] = parseFr(bytes[offset : offset+frCompressedSize])
		offset += frCompressedSize
	}

	return NewProofG1(commitment, responses), nil
}
