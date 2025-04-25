/*
Copyright SecureKey Technologies Inc. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0
*/

// Package bbs12381g2pub contains BBS+ signing primitives and keys. Although it can be used directly, it is recommended
// to use BBS+ keys created by the kms along with the framework's Crypto service.
package bbs12381g2pub

import (
	"errors"
	"fmt"
	"sort"

	ml "github.com/IBM/mathlib"
)

// nolint:gochecknoglobals
var curve = ml.Curves[ml.BLS12_381_BBS]

// BBSG2Pub defines BBS+ signature scheme where public key is a point in the field of G2.
// BBS+ signature scheme (as defined in https://eprint.iacr.org/2016/663.pdf, section 4.3).
type BBSG2Pub struct{}

// New creates a new BBSG2Pub.
func New() *BBSG2Pub {
	return &BBSG2Pub{}
}

// Number of bytes in scalar compressed form.
const frCompressedSize = 32

var (
	// nolint:gochecknoglobals
	// Signature length.
	bls12381SignatureLen = curve.CompressedG1ByteSize + 3*frCompressedSize //现在只考虑添加了cid的情况，当然加了uid也是这个

	// nolint:gochecknoglobals
	// Default BLS 12-381 public key length in G2 field.
	bls12381G2PublicKeyLen = curve.CompressedG2ByteSize

	// nolint:gochecknoglobals
	// Number of bytes in G1 X coordinate.
	g1CompressedSize = curve.CompressedG1ByteSize

	// nolint:gochecknoglobals
	// Number of bytes in G1 X and Y coordinates.
	g1UncompressedSize = curve.G1ByteSize

	// nolint:gochecknoglobals
	// Number of bytes in G2 X(a, b) and Y(a, b) coordinates.
	g2UncompressedSize = curve.G2ByteSize

	// nolint:gochecknoglobals
	// Number of bytes in scalar uncompressed form.
	frUncompressedSize = curve.ScalarByteSize
)

//+++++++++++++++++++++++++++++++04.24+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//添加盲签名的功能！！！！
//首先定义盲签名请求的结构

type BlindedSignatureRequest struct {
	BlindedIndices    []int
	NonBlindedIndices []int
	Commitment        *ml.G1
	ProofC            *ProofG1
	Cid1              *ml.G1
	ProofCid1         *ProofG1
}

// BlindSign 实现盲化签名
func (bbs *BBSG2Pub) BlindSign(input *BlindedSignatureRequest, messages [][]byte, privKeyBytes []byte) (*Signature, error) {
	if len(messages) == 0 {
		return nil, errors.New("messages are not defined")
	}

	if len(messages) != len(input.NonBlindedIndices) {
		return nil, errors.New("The number of messages is not matched with NonBlindedIndices")
	}

	privKey, err := UnmarshalPrivateKey(privKeyBytes)
	if err != nil {
		return nil, fmt.Errorf("unmarshal private key: %w", err)
	}

	pubKey := privKey.PublicKey()
	messagesCount := len(input.BlindedIndices) + len(input.NonBlindedIndices)

	pubKeyWithGenerators, err := pubKey.ToPublicKeyWithGenerators(messagesCount)
	if err != nil {
		return nil, fmt.Errorf("build generators from public key: %w", err)
	}

	basesC := make([]*ml.G1, 0, 2+len(input.BlindedIndices))
	basesC = append(basesC, pubKeyWithGenerators.h0, pubKeyWithGenerators.h02)
	for _, index := range input.BlindedIndices {
		if index >= 0 && index < len(pubKeyWithGenerators.h) {
			basesC = append(basesC, pubKeyWithGenerators.h[index])
		} else {
			fmt.Printf("Warning: Index %d is out of range of pubKey.h\n", index)
		}
	}

	challenge := frFromOKM(input.Commitment.Bytes())
	err = input.ProofC.Verify(basesC, input.Commitment, challenge)
	if err != nil {
		return nil, errors.New("bad signature request commitment")
	}

	chalcid := frFromOKM(input.Cid1.Bytes())
	baseh02 := make([]*ml.G1, 0, 1)
	baseh02 = append(baseh02, pubKeyWithGenerators.h02)
	err = input.ProofCid1.Verify(baseh02, input.Cid1, chalcid)
	if err != nil {
		return nil, errors.New("bad signature request cid commitment")
	}

	messagesFr := make([]*SignatureMessage, len(messages))
	for i := range messages {
		messagesFr[i] = ParseSignatureMessage(messages[i])
	}

	// 生成 e 和 s
	e, s2, cid2 := createRandSignatureFr(), createRandSignatureFr(), createRandSignatureFr()
	exp := privKey.FR.Copy()
	exp = exp.Plus(e)
	exp.InvModP(curve.GroupOrder)

	computeB := computeBlindedB(s2, cid2, input.NonBlindedIndices, input.Commitment, messagesFr, pubKeyWithGenerators)

	// 计算签名
	sig := computeB.Mul(frToRepr(exp))

	signature := &Signature{
		A:   sig,
		E:   e,
		S:   s2,
		CID: cid2,
	}

	return signature, nil
}

// 生成签名请求
func (bbs *BBSG2Pub) BlindedSignReq(blindedmessages [][]byte, blindedIndices []int, nonBlindedIndices []int, pubKeyBytes []byte) (*BlindedSignatureRequest, *ml.Zr, *ml.Zr, error) {
	if len(blindedIndices) != len(blindedmessages) {
		return nil, nil, nil, errors.New("The length of blinded messages does not match the length of BlindedIndices.")
	}

	messagesCount := len(blindedmessages) + len(nonBlindedIndices)

	messagesFr := make([]*SignatureMessage, len(blindedmessages))

	for i := range blindedmessages {
		messagesFr[i] = ParseSignatureMessage(blindedmessages[i])
	}

	pubKey, err := UnmarshalPublicKey(pubKeyBytes)
	if err != nil {
		return nil, nil, nil, fmt.Errorf("parse public key: %w", err)
	}

	key, err := pubKey.ToPublicKeyWithGenerators(messagesCount)
	if err != nil {
		return nil, nil, nil, fmt.Errorf("build generators from public key: %w", err)
	}

	const basesOffset = 2
	cb := newCommitmentBuilder(len(blindedmessages) + basesOffset)
	cid1, s1 := createRandSignatureFr(), createRandSignatureFr()
	cb.add(key.h0, s1)
	cb.add(key.h02, cid1)

	cb_id := newCommitmentBuilder(1)
	cb_id.add(key.h02, cid1)

	for i := 0; i < len(blindedmessages); i++ {
		cb.add(key.h[blindedIndices[i]], messagesFr[i].FR)
	}

	C := cb.build()

	Cid := cb_id.build()

	committingCid := NewProverCommittingG1()
	secretsCid := make([]*ml.Zr, 0, 1)

	committingCid.Commit(key.h02)
	secretsCid = append(secretsCid, cid1)
	pokVCid := committingCid.Finish()
	chalcid := frFromOKM(pokVCid.commitment.Bytes())

	committingC := NewProverCommittingG1()
	secretsC := make([]*ml.Zr, 0, 2+len(blindedmessages))
	committingC.Commit(key.h0)
	secretsC = append(secretsC, s1)
	committingC.Commit(key.h02)
	secretsC = append(secretsC, cid1)
	for i := 0; i < len(blindedmessages); i++ {
		committingC.Commit(key.h[blindedIndices[i]])
		sourceFR := messagesFr[i].FR
		hiddenFRCopy := sourceFR.Copy()
		secretsC = append(secretsC, hiddenFRCopy)
	}

	pokVC := committingC.Finish()
	challenge := frFromOKM(pokVC.commitment.Bytes())

	return &BlindedSignatureRequest{
		BlindedIndices:    blindedIndices,
		NonBlindedIndices: nonBlindedIndices,
		Commitment:        C,
		ProofC:            pokVC.GenerateProof(challenge, secretsC),
		Cid1:              Cid,
		ProofCid1:         pokVCid.GenerateProof(chalcid, secretsCid),
	}, s1, cid1, nil

}

// computeBlindedB 计算盲化消息的 B 值
func computeBlindedB(s2 *ml.Zr, cid2 *ml.Zr, nonBlindedIndices []int, Commitment *ml.G1, messages []*SignatureMessage, key *PublicKeyWithGenerators) *ml.G1 {
	const basesOffset = 4

	cb := newCommitmentBuilder(len(messages) + basesOffset)

	cb.add(curve.GenG1, curve.NewZrFromInt(1))
	cb.add(key.h0, s2)
	cb.add(key.h02, cid2)
	cb.add(Commitment, curve.NewZrFromInt(1))

	Ind := 0
	for _, i := range nonBlindedIndices {
		cb.add(key.h[i], messages[Ind].FR)
		Ind += 1
	}

	return cb.build()
}

func (bbs *BBSG2Pub) MergeBlindSignature(input *Signature, s1, cid1 *ml.Zr) ([]byte, error) {
	s := input.S.Copy()
	s.Plus(s1)

	cid := input.CID.Copy()
	cid.Plus(cid1)

	input.S = s
	input.CID = cid

	signature, err := input.ToBytes()
	if err != nil {
		return nil, errors.New("Cannot Merge")
	}
	return signature, nil
}

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

// Verify makes BLS BBS12-381 signature verification.
func (bbs *BBSG2Pub) Verify(messages [][]byte, sigBytes, pubKeyBytes []byte) error {
	signature, err := ParseSignature(sigBytes)
	if err != nil {
		return fmt.Errorf("parse signature: %w", err)
	}

	pubKey, err := UnmarshalPublicKey(pubKeyBytes)
	if err != nil {
		return fmt.Errorf("parse public key: %w", err)
	}

	messagesCount := len(messages)

	publicKeyWithGenerators, err := pubKey.ToPublicKeyWithGenerators(messagesCount)
	if err != nil {
		return fmt.Errorf("build generators from public key: %w", err)
	}

	messagesFr := messagesToFr(messages)

	return signature.Verify(messagesFr, publicKeyWithGenerators)
}

// Sign signs the one or more messages using private key in compressed form.
func (bbs *BBSG2Pub) Sign(messages [][]byte, privKeyBytes []byte) ([]byte, error) {
	privKey, err := UnmarshalPrivateKey(privKeyBytes)
	if err != nil {
		return nil, fmt.Errorf("unmarshal private key: %w", err)
	}

	if len(messages) == 0 {
		return nil, errors.New("messages are not defined")
	}

	return bbs.SignWithKey(messages, privKey)
}

// VerifyProof verifies BBS+ signature proof for one ore more revealed messages.
func (bbs *BBSG2Pub) VerifyProof(messagesBytes [][]byte, proof, nonce, pubKeyBytes []byte) error {
	payload, err := parsePoKPayload(proof)
	if err != nil {
		return fmt.Errorf("parse signature proof: %w", err)
	}

	signatureProof, err := ParseSignatureProof(proof[payload.lenInBytes():])
	if err != nil {
		return fmt.Errorf("parse signature proof: %w", err)
	}

	messages := messagesToFr(messagesBytes)

	pubKey, err := UnmarshalPublicKey(pubKeyBytes)
	if err != nil {
		return fmt.Errorf("parse public key: %w", err)
	}

	publicKeyWithGenerators, err := pubKey.ToPublicKeyWithGenerators(payload.messagesCount)
	if err != nil {
		return fmt.Errorf("build generators from public key: %w", err)
	}

	if len(payload.revealed) > len(messages) {
		return fmt.Errorf("payload revealed bigger from messages")
	}

	revealedMessages := make(map[int]*SignatureMessage)
	for i := range payload.revealed {
		revealedMessages[payload.revealed[i]] = messages[i]
	}

	challengeBytes := signatureProof.GetBytesForChallenge(revealedMessages, publicKeyWithGenerators)
	proofNonce := ParseProofNonce(nonce)
	proofNonceBytes := proofNonce.ToBytes()
	challengeBytes = append(challengeBytes, proofNonceBytes...)
	proofChallenge := frFromOKM(challengeBytes)

	return signatureProof.Verify(proofChallenge, publicKeyWithGenerators, revealedMessages, messages)
}

// DeriveProof derives a proof of BBS+ signature with some messages disclosed.
func (bbs *BBSG2Pub) DeriveProof(messages [][]byte, sigBytes, nonce, pubKeyBytes []byte,
	revealedIndexes []int) ([]byte, error) {
	if len(revealedIndexes) == 0 {
		return nil, errors.New("no message to reveal")
	}

	sort.Ints(revealedIndexes)

	messagesCount := len(messages)

	messagesFr := messagesToFr(messages)

	pubKey, err := UnmarshalPublicKey(pubKeyBytes)
	if err != nil {
		return nil, fmt.Errorf("parse public key: %w", err)
	}

	publicKeyWithGenerators, err := pubKey.ToPublicKeyWithGenerators(messagesCount)
	if err != nil {
		return nil, fmt.Errorf("build generators from public key: %w", err)
	}

	signature, err := ParseSignature(sigBytes)
	if err != nil {
		return nil, fmt.Errorf("parse signature: %w", err)
	}

	pokSignature, err := NewPoKOfSignature(signature, messagesFr, revealedIndexes, publicKeyWithGenerators)
	if err != nil {
		return nil, fmt.Errorf("init proof of knowledge signature: %w", err)
	}

	challengeBytes := pokSignature.ToBytes()

	proofNonce := ParseProofNonce(nonce)
	proofNonceBytes := proofNonce.ToBytes()
	challengeBytes = append(challengeBytes, proofNonceBytes...)

	proofChallenge := frFromOKM(challengeBytes)

	proof := pokSignature.GenerateProof(proofChallenge)

	payload := newPoKPayload(messagesCount, revealedIndexes)

	payloadBytes, err := payload.toBytes()
	if err != nil {
		return nil, fmt.Errorf("derive proof: paylod to bytes: %w", err)
	}

	signatureProofBytes := append(payloadBytes, proof.ToBytes()...)

	return signatureProofBytes, nil
}

// SignWithKey signs the one or more messages using BBS+ key pair.
func (bbs *BBSG2Pub) SignWithKey(messages [][]byte, privKey *PrivateKey) ([]byte, error) {
	var err error

	pubKey := privKey.PublicKey()
	messagesCount := len(messages)

	pubKeyWithGenerators, err := pubKey.ToPublicKeyWithGenerators(messagesCount)
	if err != nil {
		return nil, fmt.Errorf("build generators from public key: %w", err)
	}

	messagesFr := make([]*SignatureMessage, len(messages))
	for i := range messages {
		messagesFr[i] = ParseSignatureMessage(messages[i])
	}
	//Add CID2
	e, s, cid := createRandSignatureFr(), createRandSignatureFr(), createRandSignatureFr()
	exp := privKey.FR.Copy()
	exp = exp.Plus(e)
	exp.InvModP(curve.GroupOrder)

	b := computeB(s, cid, messagesFr, pubKeyWithGenerators)

	sig := b.Mul(frToRepr(exp))

	signature := &Signature{
		A:   sig,
		E:   e,
		S:   s,
		CID: cid,
	}

	return signature.ToBytes()
}

// 修改后增加cid
// 不是，woc这里不支持盲签名？？！！！！
// 算了，不耽误，先这样吧
func computeB(s *ml.Zr, cid *ml.Zr, messages []*SignatureMessage, key *PublicKeyWithGenerators) *ml.G1 {
	const basesOffset = 3 //新增cid

	cb := newCommitmentBuilder(len(messages) + basesOffset)

	cb.add(curve.GenG1, curve.NewZrFromInt(1))
	cb.add(key.h0, s)
	//增加：
	cb.add(key.h02, cid)

	for i := 0; i < len(messages); i++ {
		cb.add(key.h[i], messages[i].FR)
	}

	return cb.build()
}

type commitmentBuilder struct {
	bases   []*ml.G1
	scalars []*ml.Zr
}

func newCommitmentBuilder(expectedSize int) *commitmentBuilder {
	return &commitmentBuilder{
		bases:   make([]*ml.G1, 0, expectedSize),
		scalars: make([]*ml.Zr, 0, expectedSize),
	}
}

func (cb *commitmentBuilder) add(base *ml.G1, scalar *ml.Zr) {
	cb.bases = append(cb.bases, base)
	cb.scalars = append(cb.scalars, scalar)
}

func (cb *commitmentBuilder) build() *ml.G1 {
	return sumOfG1Products(cb.bases, cb.scalars)
}

func sumOfG1Products(bases []*ml.G1, scalars []*ml.Zr) *ml.G1 {
	var res *ml.G1

	for i := 0; i < len(bases); i++ {
		b := bases[i]
		s := scalars[i]

		g := b.Mul(frToRepr(s))
		if res == nil {
			res = g
		} else {
			res.Add(g)
		}
	}

	return res
}

func compareTwoPairings(p1 *ml.G1, q1 *ml.G2,
	p2 *ml.G1, q2 *ml.G2) bool {
	p := curve.Pairing2(q1, p1, q2, p2)
	p = curve.FExp(p)

	return p.IsUnity()
}

// ProofNonce is a nonce for Proof of Knowledge proof.
type ProofNonce struct {
	fr *ml.Zr
}

// ParseProofNonce creates a new ProofNonce from bytes.
func ParseProofNonce(proofNonceBytes []byte) *ProofNonce {
	return &ProofNonce{
		frFromOKM(proofNonceBytes),
	}
}

// ToBytes converts ProofNonce into bytes.
func (pn *ProofNonce) ToBytes() []byte {
	return frToRepr(pn.fr).Bytes()
}
