/*
Copyright SecureKey Technologies Inc. All Rights Reserved.

SPDX-License-Identifier: Apache-2.0
*/

package bbs12381g2pub

import (
	"crypto/rand"

	ml "github.com/IBM/mathlib"
	"golang.org/x/crypto/blake2b"
)

func parseFr(data []byte) *ml.Zr {
	return curve.NewZrFromBytes(data)
}

// nolint:gochecknoglobals
var f2192Bytes = []byte{
	0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1,
	0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
	0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
	0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
} //调整生成的随机数的范围

func f2192() *ml.Zr {
	return curve.NewZrFromBytes(f2192Bytes)
}

// 简单看作Msg-->Zr的hash func
/* 功能：将任意消息哈希并映射到特定有限域中的伪随机元素。
   核心步骤：哈希 → 分割 → 字节转换 → 域运算。
*/
func frFromOKM(message []byte) *ml.Zr {
	const (
		eightBytes = 8
		okmMiddle  = 24
	)

	// We pass a null key so error is impossible here.
	h, _ := blake2b.New384(nil) //nolint:errcheck

	// blake2b.digest() does not return an error.
	_, _ = h.Write(message)
	okm := h.Sum(nil)
	emptyEightBytes := make([]byte, eightBytes)

	elm := curve.NewZrFromBytes(append(emptyEightBytes, okm[:okmMiddle]...))
	elm = elm.Mul(f2192())

	fr := curve.NewZrFromBytes(append(emptyEightBytes, okm[okmMiddle:]...))
	elm = elm.Plus(fr)

	return elm
}

func frToRepr(fr *ml.Zr) *ml.Zr {
	return fr.Copy()
}

// 把需要签名的消息映射至Zr
func messagesToFr(messages [][]byte) []*SignatureMessage {
	messagesFr := make([]*SignatureMessage, len(messages))

	for i := range messages {
		messagesFr[i] = ParseSignatureMessage(messages[i])
	}

	return messagesFr
}

// 简单看作随机数生成器
func createRandSignatureFr() *ml.Zr {
	return curve.NewRandomZr(rand.Reader)
}
