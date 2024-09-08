/-
Copyright (c) 2024 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Aut
import Mathlib.Data.Finite.Card

lemma AlgEquiv.card_le (R : Type*) (A : Type*) (B : Type*)
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] [Fintype (A ≃ₐ[R] B)] [Fintype (A →ₐ[R] B)] :
    Fintype.card (A ≃ₐ[R] B) ≤ Fintype.card (A →ₐ[R] B) :=
  Fintype.card_le_of_injective _ coe_algHom_injective

lemma AlgEquiv.natCard_le (R : Type*) (A : Type*) (B : Type*)
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] [Finite (A →ₐ[R] B)] :
    Nat.card (A ≃ₐ[R] B) ≤ Nat.card (A →ₐ[R] B) :=
  Finite.card_le_of_injective _ coe_algHom_injective
