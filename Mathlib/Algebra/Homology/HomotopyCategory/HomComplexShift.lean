/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
--import Mathlib.Tactic.Ring

/-! Shifting cochains

Let `C` be a preadditive category. Given two cochain complexes (indexed by `ℤ`),
the type of cochains `HomComplex.Cochain K L n` of degree `n` was introduced
in `Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`. In this file, we
study how these cochains behave with respect to the shift on the complexes `K`
and `L`.

When `n`, `a`, `n'` are integers such that `h : n' + a = n`,
we obtain `rightShiftAddEquiv K L n a n' h : Cochain K L n ≃+ Cochain K L⟦a⟧ n'`.
This definition does not involve signs, but the analogous definition for
the shift on the first variable `K` shall involve signs, as we follow the
conventions appearing in the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000].

## References
* [Brian Conrad, Grothendieck duality and base change][conrad2000]

-/

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

namespace CochainComplex

variable {K L M : CochainComplex C ℤ} {n : ℤ}

namespace HomComplex

namespace Cochain

variable (γ γ₁ γ₂ : Cochain K L n)

def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain K (L⟦a⟧) n' :=
  Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by linarith)).inv)

lemma rightShift_v (a n' : ℤ) (hn' : n' + a = n) (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p + n = p') :
    (γ.rightShift a n' hn').v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a q p' (by rw [← hp', ← hpq, ← hn', add_assoc])).inv := by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

def rightUnshift {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => γ.v p (p + n') rfl ≫
    (L.shiftFunctorObjXIso a (p + n') q (by rw [← hpq, add_assoc, hn])).hom)

lemma rightUnshift_v {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n)
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p + n' = p') :
    (γ.rightUnshift n hn).v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a p' q (by rw [← hpq, ← hn, ← add_assoc, hp'])).hom := by
  subst hp'
  dsimp only [rightUnshift]
  simp only [mk_v]

@[simp]
lemma rightUnshift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (γ.rightShift a n' hn').rightUnshift n hn' = γ := by
  ext p q hpq
  simp only [rightUnshift_v _ n hn' p q hpq (p + n') rfl,
    γ.rightShift_v _ _ hn' p (p + n') rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.inv_hom_id, comp_id]

variable {G}

@[simp]
lemma rightShift_rightUnshift {a n' : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn' : n' + a = n) :
    (γ.rightUnshift n hn').rightShift a n' hn' = γ := by
  ext p q hpq
  simp only [(γ.rightUnshift n hn').rightShift_v a n' hn' p q hpq (p + n) rfl,
    γ.rightUnshift_v n hn' p (p + n) rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.hom_inv_id, comp_id]

variable (K L)

@[simp]
lemma rightShift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain K L n).rightShift a n' hn' = 0 := by
  ext p q hpq
  dsimp
  rw [rightShift_v _ a n' hn' p q hpq _ rfl, zero_v, zero_comp]

variable (n)

@[simp]
lemma rightUnshift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain K (L⟦a⟧) n').rightUnshift n hn' = 0 := by
  ext p q hpq
  dsimp
  rw [rightUnshift_v _ n _ _ _ _ (q - a) (by linarith), zero_v, zero_comp]

variable {K L n}

@[simp]
lemma rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
  (-γ).rightShift a n' hn' = -γ.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, neg_v, neg_comp]

@[simp]
lemma rightShift_add (a n' : ℤ) (hn' : n' + a = n) :
  (γ₁ + γ₂).rightShift a n' hn' = γ₁.rightShift a n' hn' + γ₂.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, add_v, add_comp]

variable (K L)

@[simps]
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain K L n ≃+ Cochain K (L⟦a⟧) n' where
  toFun γ := γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by simp
  right_inv γ := by simp
  map_add' γ γ' := by simp

variable {K L}

@[simp]
lemma rightShift_smul (a n' : ℤ) (hn' : n' + a = n) (x : R) :
  (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, smul_v, Linear.smul_comp]

@[simp]
lemma rightShift_units_smul (a n' : ℤ) (hn' : n' + a = n) (x : Rˣ) :
  (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  apply rightShift_smul


@[simp]
def rightUnshift_smul {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) (x : R) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  ext p q hpq
  dsimp
  simp only [rightUnshift_v _ n hn p q hpq _ rfl, smul_v, Linear.smul_comp]

@[simp]
def rightUnshift_units_smul {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ)
    (hn : n' + a = n) (x : Rˣ) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  apply rightUnshift_smul

lemma rightUnshift_comp {m : ℤ} {a : ℤ} (γ' : Cochain L (M⟦a⟧) m) {nm : ℤ} (hnm : n + m = nm)
    (nm' : ℤ) (hnm' : nm + a = nm') (m' : ℤ) (hm' : m + a = m') :
    (γ.comp γ' hnm).rightUnshift nm' hnm' =
      γ.comp (γ'.rightUnshift m' hm') (by linarith) := by
  ext p q hpq
  rw [(γ.comp γ' hnm).rightUnshift_v nm' hnm' p q hpq (p + n + m) (by linarith),
    γ.comp_v γ' hnm p (p + n) (p + n + m) rfl rfl,
    comp_v _ _ (show n + m' = nm' by linarith) p (p + n) q (by linarith) (by linarith),
    γ'.rightUnshift_v m' hm' (p + n) q (by linarith) (p + n + m) rfl, assoc]

lemma δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (γ.rightShift a n' hn') = a.negOnePow • (δ n m γ).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by linarith
    ext p q hpq
    dsimp
    rw [(δ n m γ).rightShift_v a m' hm' p q hpq _ rfl,
      δ_v n m hnm _ p (p+m) rfl (p+n) (p+1) (by linarith) rfl,
      δ_v n' m' hnm' _ p q hpq (p+n') (p+1) (by linarith) rfl,
      γ.rightShift_v a n' hn' p (p+n') rfl (p+n) rfl,
      γ.rightShift_v a n' hn' (p+1) q _ (p+m) (by linarith)]
    simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, ComplexShape.up_Rel, shiftFunctor_obj_d',
      Linear.comp_units_smul, assoc, HomologicalComplex.XIsoOfEq_inv_comp_d, not_true_eq_false,
      add_comp, HomologicalComplex.d_comp_XIsoOfEq_inv, Linear.units_smul_comp, smul_add,
      add_right_inj, smul_smul]
    congr 1
    rw [← hm', add_comm m', Int.negOnePow_add, ← mul_assoc,
      Int.units_mul_self, one_mul]
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by linarith)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, rightShift_zero, smul_zero]

lemma δ_rightUnshift {a n' : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) (m m' : ℤ) (hm' : m' + a = m) :
    δ n m (γ.rightUnshift n hn) = a.negOnePow • (δ n' m' γ).rightUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (rightShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [rightUnshift_rightShift, γ'.δ_rightShift a n' m' hn m hm', rightUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

end Cochain

namespace Cocycle

variable (γ : Cocycle K L n)

@[simps!]
def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cocycle K (L⟦a⟧) n' :=
  Cocycle.mk (γ.1.rightShift a n' hn') _ rfl (by
    simp only [Cochain.δ_rightShift _ a n' (n'+1) hn' (n+1) (by linarith),
      δ_eq_zero, Cochain.rightShift_zero, smul_zero])

@[simps!]
def rightUnshift {n' a : ℤ} (γ : Cocycle K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    Cocycle K L n :=
  Cocycle.mk (γ.1.rightUnshift n hn) _ rfl (by
    rw [Cochain.δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by linarith),
      δ_eq_zero, Cochain.rightUnshift_zero, smul_zero])

end Cocycle

end HomComplex

end CochainComplex
