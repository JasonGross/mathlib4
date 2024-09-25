/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone.Basic
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Fundamental Cone

In this file, we study the subset `NormLessThanOne` of the `fundamentalCone` defined as the
subset of elements `x` in the `fundamentalCone` such that `mixedEmbedding.norm x ≤ 1`.

Mainly, we want to prove that its frontier has volume zero and compute its volume. For this, we
follow in part the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

## Strategy of proof

* `polarCoordMixedSpace` and `lintegral_eq_lintegral_polarCoordMixedSpace_symm`



-/

variable (K : Type*) [Field K]

open Bornology NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem

open scoped Real

namespace NumberField.mixedEmbedding

noncomputable section realSpace

/-- DOCSTRING -/
abbrev realSpace := InfinitePlace K → ℝ

variable {K}

/-- DOCSTRING -/
def realToMixed : (realSpace K) →L[ℝ] (mixedSpace K) := ContinuousLinearMap.prod
  (ContinuousLinearMap.pi fun w ↦ ContinuousLinearMap.proj w.val)
  (ContinuousLinearMap.pi fun w ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj w.val))

@[simp]
theorem realToMixed_apply_of_isReal (x :realSpace K) {w : InfinitePlace K}
    (hw : IsReal w) : (realToMixed x).1 ⟨w, hw⟩ = x w := rfl

@[simp]
theorem realToMixed_apply_of_isComplex (x : realSpace K) {w : InfinitePlace K}
    (hw : IsComplex w) : (realToMixed x).2 ⟨w, hw⟩ = x w := rfl

@[simp]
theorem normAtPlace_realToMixed (w : InfinitePlace K) (x : realSpace K) :
    normAtPlace w (realToMixed x) = ‖x w‖ := by
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtPlace_apply_isReal hw, realToMixed]
  · simp [normAtPlace_apply_isComplex hw, realToMixed]

@[simp]
theorem norm_realToMixed [NumberField K] (x : realSpace K) :
    mixedEmbedding.norm (realToMixed x) = ∏ w, ‖x w‖ ^ w.mult :=
  Finset.prod_congr rfl fun w _ ↦ by simp

theorem pos_norm_realToMixed [NumberField K] {x : realSpace K} (hx : ∀ w, x w ≠ 0) :
    0 < mixedEmbedding.norm (realToMixed x) := by
  rw [norm_realToMixed]
  exact Finset.prod_pos fun w _ ↦ pow_pos (abs_pos.mpr (hx w)) _

theorem logMap_realToMixed [NumberField K] {x : realSpace K}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    logMap (realToMixed x) = fun w ↦ (mult w.val) * Real.log (x w.val) := by
  ext
  rw [logMap_apply_of_norm_one hx, normAtPlace_realToMixed, Real.norm_eq_abs, Real.log_abs]

open Classical in
/-- DOCSTRING -/
def mixedToReal (x : mixedSpace K) : realSpace K :=
    fun w ↦ if hw : IsReal w then x.1 ⟨w, hw⟩ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖

@[simp]
theorem mixedToReal_apply_of_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    mixedToReal x w.val = x.1 w := by
  rw [mixedToReal, dif_pos]

theorem mixedToReal_apply_of_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    mixedToReal x w.val = ‖x.2 w‖ := by
  rw [mixedToReal, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]

theorem mixedToReal_nonneg  (x : mixedSpace K) (w : {w // IsComplex w}) :
    0 ≤ mixedToReal x w.val := by
  rw [mixedToReal_apply_of_isComplex]
  exact norm_nonneg _

theorem mixedToReal_smul (x : mixedSpace K) {r : ℝ} (hr : 0 ≤ r) :
    mixedToReal (r • x) = r • mixedToReal x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [Pi.smul_apply, mixedToReal_apply_of_isReal _ ⟨w, hw⟩, Prod.smul_fst, Pi.smul_apply]
  · simp_rw [Pi.smul_apply, mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, Prod.smul_snd, Pi.smul_apply,
      _root_.norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, smul_eq_mul]

open Classical in
theorem realToMixedToReal (x : realSpace K) :
    mixedToReal (realToMixed x) = fun w ↦ if IsReal w then x w else ‖x w‖ := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal _ ⟨w, hw⟩, realToMixed_apply_of_isReal _ hw, if_pos hw]
  · rw [mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, if_neg (not_isReal_iff_isComplex.mpr hw),
      realToMixed_apply_of_isComplex, Complex.norm_real, Real.norm_eq_abs]

@[simp]
theorem realToMixedToReal_eq_self_of_nonneg {x : realSpace K} (hx : ∀ w, IsComplex w → 0 ≤ x w) :
    mixedToReal (realToMixed x) = x := by
  rw [realToMixedToReal]
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [if_pos hw]
  · rw [if_neg (not_isReal_iff_isComplex.mpr hw), Real.norm_eq_abs, abs_of_nonneg (hx w hw)]

theorem mixedToRealToMixed (x : mixedSpace K) :
    realToMixed (mixedToReal x) = (fun w ↦ x.1 w, fun w ↦ (‖x.2 w‖ : ℂ)) := by
  ext w
  · rw [realToMixed_apply_of_isReal, mixedToReal_apply_of_isReal]
  · rw [realToMixed_apply_of_isComplex, mixedToReal_apply_of_isComplex]

theorem norm_mixedToReal (x : mixedSpace K) (w : InfinitePlace K) :
    ‖mixedToReal x w‖ = normAtPlace w x := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal _ ⟨w, hw⟩, normAtPlace_apply_isReal]
  · rw [mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, normAtPlace_apply_isComplex, norm_norm]

theorem norm_mixedToRealToMixed [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm (realToMixed (mixedToReal x)) = mixedEmbedding.norm x := by
  simp_rw [norm_realToMixed, norm_mixedToReal, mixedEmbedding.norm_apply]

@[simp]
theorem logMap_mixedToRealToMixed_of_norm_one [NumberField K] {x : mixedSpace K}
    (hx : mixedEmbedding.norm x = 1) : logMap (realToMixed (mixedToReal x)) = logMap x := by
  ext
  rw [logMap_apply_of_norm_one hx, logMap_apply_of_norm_one (by rwa [norm_mixedToRealToMixed]),
    normAtPlace_realToMixed, ← norm_mixedToReal]

open Classical in
theorem norm_realToMixed_prod_units_rpow [NumberField K] {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (u : ι → (𝓞 K)ˣ) :
    mixedEmbedding.norm (realToMixed fun w : InfinitePlace K ↦ ∏ i, w (u i) ^ c i) = 1 :=
  calc
  _ = |∏ w : InfinitePlace K, ∏ i, (w (u i) ^ c i) ^ w.mult| := by
    simp_rw [norm_realToMixed, Real.norm_eq_abs, Finset.abs_prod, abs_pow, Finset.prod_pow]
  _ = |∏ w : InfinitePlace K, ∏ i, (w (u i) ^ w.mult) ^ c i| := by
    simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (apply_nonneg _ _), mul_comm]
  _ = |∏ i, (∏ w : InfinitePlace K, (w (u i) ^ w.mult)) ^ c i| := by
    rw [Finset.prod_comm]
    simp_rw [Real.finset_prod_rpow _ _ (fun _ _ ↦ pow_nonneg (apply_nonneg _ _) _)]
  _ = 1 := by
    simp_rw [prod_eq_abs_norm, Units.norm, Rat.cast_one, Real.one_rpow,
      Finset.prod_const_one, abs_one]

end realSpace

noncomputable section polarCoord

open MeasureTheory MeasureTheory.Measure MeasurableEquiv

open Classical in
/-- DOCSTRING -/
def realProdComplexProdMeasurableEquiv :
    ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ) ≃ᵐ
       (realSpace K) × ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  MeasurableEquiv.trans (prodCongr (refl _)
      (arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans prodAssoc.symm <|
       MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

open Classical in
/-- DOCSTRING -/
def realProdComplexProdEquiv :
    ({w : InfinitePlace K // IsReal w} → ℝ) ×
      ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ) ≃ₜ
        (realSpace K) × ({w : InfinitePlace K // IsComplex w} → ℝ) where
  __ := realProdComplexProdMeasurableEquiv K
  continuous_toFun := by
    change Continuous fun x ↦ ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩
    refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
    by_cases hw : IsReal w
    · simp_rw [dif_pos hw]; fun_prop
    · simp_rw [dif_neg hw]; fun_prop
  continuous_invFun := by
    change Continuous fun x ↦ (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩)
    fun_prop

open Classical in
theorem volume_preserving_realProdComplexProdEquiv [NumberField K] :
    MeasurePreserving (realProdComplexProdEquiv K) := by
  change MeasurePreserving (realProdComplexProdMeasurableEquiv K) volume volume
  exact MeasurePreserving.trans ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ {w : InfinitePlace K // IsComplex w})) <|
    MeasurePreserving.trans (volume_preserving_prodAssoc.symm) <|
      MeasurePreserving.trans
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
        (MeasurableEquiv.refl ℝ)
          (MeasurePreserving.id volume))).prod (MeasurePreserving.id volume))
      <| ((volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
        (fun w : InfinitePlace K ↦ IsReal w)).symm).prod (MeasurePreserving.id volume)

open Classical in
@[simp]
theorem realProdComplexProdEquiv_apply (x : ({w : InfinitePlace K // IsReal w} → ℝ) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)) :
    realProdComplexProdEquiv K x = ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

@[simp]
theorem realProdComplexProdEquiv_symm_apply (x : (realSpace K) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    (realProdComplexProdEquiv K).symm x = (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩) := rfl

variable [NumberField K]

/-- DOCSTRING -/
def polarCoordMixedSpace : PartialHomeomorph
    (mixedSpace K) ((realSpace K) × ({w : InfinitePlace K // IsComplex w} → ℝ)) :=
  ((PartialHomeomorph.refl _).prod
    (PartialHomeomorph.pi fun _ ↦ Complex.polarCoord)).transHomeomorph (realProdComplexProdEquiv K)

theorem polarCoordMixedSpace_source :
    (polarCoordMixedSpace K).source = Set.univ ×ˢ Set.univ.pi fun _ ↦ Complex.slitPlane := by
  simp [polarCoordMixedSpace, Complex.polarCoord_source]

open Classical in
theorem polarCoordMixedSpace_target : (polarCoordMixedSpace K).target =
  (Set.univ.pi fun w ↦
      if IsReal w then Set.univ else Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π):= by
  rw [polarCoordMixedSpace, PartialHomeomorph.transHomeomorph_target]
  ext
  simp_rw [Set.mem_preimage, realProdComplexProdEquiv_symm_apply, PartialHomeomorph.prod_target,
    Set.mem_prod, PartialHomeomorph.refl_target, PartialHomeomorph.pi_target,
    Complex.polarCoord_target]
  aesop

theorem polarCoordMixedSpace_symm_apply (x : (realSpace K) × ({w // IsComplex w} → ℝ)) :
    (polarCoordMixedSpace K).symm x = ⟨fun w ↦ x.1 w.val,
      fun w ↦ Complex.polarCoord.symm (x.1 w, x.2 w)⟩ := rfl

theorem measurableSet_polarCoordMixedSpace_target :
    MeasurableSet (polarCoordMixedSpace K).target :=
  (polarCoordMixedSpace K).open_target.measurableSet

theorem polarCoordMixedSpace_apply (x : mixedSpace K) :
    polarCoordMixedSpace K x =
      (realProdComplexProdEquiv K) (x.1, fun w ↦ Complex.polarCoord (x.2 w)) := by
  rw [polarCoordMixedSpace]
  simp_rw [PartialHomeomorph.transHomeomorph_apply, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Function.comp_apply]
  rfl

theorem continuous_polarCoordMixedSpace_symm :
    Continuous (polarCoordMixedSpace K).symm := by
  change Continuous (fun x ↦ (polarCoordMixedSpace K).symm x)
  simp_rw [polarCoordMixedSpace_symm_apply]
  rw [continuous_prod_mk]
  exact ⟨by fun_prop,
    continuous_pi_iff.mpr fun i ↦ Complex.continuous_polarCoord_symm.comp' (by fun_prop)⟩

theorem realProdComplexProdEquiv_preimage_target :
  (realProdComplexProdEquiv K) ⁻¹' (polarCoordMixedSpace K).target =
    Set.univ ×ˢ Set.univ.pi fun _ ↦ polarCoord.target := by
  ext
  simp_rw [polarCoordMixedSpace_target, Set.mem_preimage, realProdComplexProdEquiv_apply,
    polarCoord_target, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, true_and,
    Set.mem_ite_univ_left, not_isReal_iff_isComplex, Set.mem_prod]
  refine ⟨fun ⟨h₁, h₂⟩ i ↦ ⟨?_, h₂ i⟩, fun h ↦ ⟨fun i hi ↦ ?_, fun i ↦ (h i).2⟩⟩
  · specialize h₁ i i.prop
    rwa [dif_neg (not_isReal_iff_isComplex.mpr i.prop)] at h₁
  · rw [dif_neg (not_isReal_iff_isComplex.mpr hi)]
    exact (h ⟨i, hi⟩).1

open Classical in
theorem lintegral_eq_lintegral_polarCoordMixedSpace_symm (f : (mixedSpace K) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ x, f x =
      ∫⁻ x in (polarCoordMixedSpace K).target,
        (∏ w : {w // IsComplex w}, (x.1 w.val).toNNReal) *
          f ((polarCoordMixedSpace K).symm x) := by
  have h : Measurable fun x ↦ (∏ w : { w // IsComplex w}, (x.1 w.val).toNNReal) *
      f ((polarCoordMixedSpace K).symm x) := by
    refine Measurable.mul ?_ ?_
    · exact measurable_coe_nnreal_ennreal_iff.mpr <| Finset.measurable_prod _ fun _ _ ↦ by fun_prop
    · exact hf.comp' (continuous_polarCoordMixedSpace_symm K).measurable
  rw [← (volume_preserving_realProdComplexProdEquiv K).setLIntegral_comp_preimage
    (measurableSet_polarCoordMixedSpace_target K) h, volume_eq_prod, volume_eq_prod,
    lintegral_prod _ hf.aemeasurable]
  simp_rw [Complex.lintegral_pi_comp_polarCoord_symm _ (hf.comp' measurable_prod_mk_left)]
  rw [realProdComplexProdEquiv_preimage_target, ← Measure.restrict_prod_eq_univ_prod,
    lintegral_prod _ (h.comp' (realProdComplexProdEquiv K).measurable).aemeasurable]
  simp_rw [realProdComplexProdEquiv_apply, polarCoordMixedSpace_symm_apply,
    dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]

end polarCoord

noncomputable section mapToUnitsPow

open FiniteDimensional Finset

variable [NumberField K]

open Classical in
/-- DOCSTRING -/
-- This cannot be a `PartiaHomeomorph` because the target is not an open set
def mapToUnitsPow₀_aux :
    PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (realSpace K) where
  toFun := fun c w ↦ if hw : w = w₀ then
      Real.exp (- ((w₀ : InfinitePlace K).mult : ℝ)⁻¹ * ∑ w : {w // w ≠ w₀}, c w)
    else Real.exp ((w.mult : ℝ)⁻¹ * c ⟨w, hw⟩)
  invFun := fun x w ↦ w.val.mult * Real.log (x w.val)
  source := Set.univ
  target := {x | ∀ w, 0 < x w} ∩ {x | ∑ w, w.mult * Real.log (x w) = 0}
  map_source' _ _ := by
    dsimp only
    refine ⟨Set.mem_setOf.mpr fun w ↦ by split_ifs <;> exact Real.exp_pos _, ?_⟩
    simp_rw [Set.mem_setOf_eq, ← Finset.univ.sum_erase_add _ (mem_univ w₀), dif_pos]
    rw [sum_subtype _ (by aesop : ∀ w, w ∈ univ.erase w₀ ↔ w ≠ w₀)]
    conv_lhs => enter [1,2,w]; rw [dif_neg w.prop]
    simp_rw [Real.log_exp, neg_mul, mul_neg, mul_inv_cancel_left₀ mult_coe_ne_zero,
      add_neg_eq_zero]
    infer_instance
  map_target' _ _ := trivial
  left_inv' := by
    intro x _
    dsimp only
    ext w
    rw [dif_neg w.prop, Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' := by
    intro x hx
    ext w
    dsimp only
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, ← sum_subtype _
        (by aesop : ∀ w, w ∈ univ.erase w₀ ↔ w ≠ w₀) (fun w ↦ w.mult * Real.log (x w))]
      rw [sum_erase_eq_sub (mem_univ w₀), hx.2, _root_.zero_sub, neg_mul, mul_neg,
        neg_neg, inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx.1 w₀)]
    · rw [dif_neg hw, inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx.1 w)]

theorem mapToUnitsPow₀_aux_symm_apply (x : realSpace K) :
    (mapToUnitsPow₀_aux K).symm x = fun w ↦ w.val.mult * Real.log (x w.val) := rfl

theorem continuous_mapToUnitsPow₀_aux :
    Continuous (mapToUnitsPow₀_aux K) := by
  unfold mapToUnitsPow₀_aux
  refine continuous_pi_iff.mpr fun w ↦ ?_
  by_cases hw : w = w₀
  · simp_rw [dif_pos hw]
    fun_prop
  · simp_rw [dif_neg hw]
    fun_prop

variable {K}

/-- DOCSTRING -/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

variable (K)

open Classical in
/-- DOCSTRING -/
-- This cannot be a `PartiaHomeomorph` because the target is not an open set
def mapToUnitsPow₀ :
    PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (realSpace K) :=
  (((basisUnitLattice K).ofZLatticeBasis ℝ).reindex
    equivFinRank).equivFun.symm.toEquiv.toPartialEquiv.trans (mapToUnitsPow₀_aux K)

theorem mapToUnitsPow₀_source :
    (mapToUnitsPow₀ K).source = Set.univ := by simp [mapToUnitsPow₀, mapToUnitsPow₀_aux]

theorem mapToUnitsPow₀_target :
    (mapToUnitsPow₀ K).target = {x | (∀ w, 0 < x w) ∧ mixedEmbedding.norm (realToMixed x) = 1} := by
  rw [mapToUnitsPow₀, mapToUnitsPow₀_aux]
  dsimp
  ext x
  simp_rw [Set.inter_univ, Set.mem_inter_iff, Set.mem_setOf, and_congr_right_iff]
  intro hx
  rw [← Real.exp_injective.eq_iff, Real.exp_zero, Real.exp_sum, norm_realToMixed]
  refine Eq.congr (Finset.prod_congr rfl fun _ _ ↦ ?_) rfl
  rw [← Real.log_rpow (hx _), Real.exp_log (Real.rpow_pos_of_pos (hx _) _), Real.norm_eq_abs,
    abs_of_pos (hx _), Real.rpow_natCast]

variable {K}

theorem mixedToReal_mem_target {x : mixedSpace K} (hx₁ : ∀ w, 0 < x.1 w)
    (hx₂ : mixedEmbedding.norm x = 1):
    mixedToReal x ∈ (mapToUnitsPow₀ K).target := by
  rw [mapToUnitsPow₀_target]
  refine ⟨fun w ↦ ?_, by rwa [norm_mixedToRealToMixed]⟩
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal _ ⟨w, hw⟩]
    exact hx₁ _
  · refine lt_of_le_of_ne' (mixedToReal_nonneg _ ⟨w, hw⟩) ?_
    contrapose! hx₂
    rw [mixedToReal_apply_of_isComplex _ ⟨w, hw⟩] at hx₂
    rw [mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, by rwa [normAtPlace_apply_isComplex hw x]⟩]
    exact zero_ne_one

theorem norm_mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm (realToMixed (mapToUnitsPow₀ K c)) = 1 := by
  suffices mapToUnitsPow₀ K c ∈ (mapToUnitsPow₀ K).target by
    rw [mapToUnitsPow₀_target] at this
    exact this.2
  refine PartialEquiv.map_source (mapToUnitsPow₀ K) ?_
  rw [mapToUnitsPow₀_source]
  exact trivial

theorem mapToUnitsPow₀_pos (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) (w : InfinitePlace K) :
    0 < mapToUnitsPow₀ K c w := by
  suffices mapToUnitsPow₀ K c ∈ (mapToUnitsPow₀ K).target by
    rw [mapToUnitsPow₀_target] at this
    exact this.1 w
  refine PartialEquiv.map_source (mapToUnitsPow₀ K) ?_
  rw [mapToUnitsPow₀_source]
  exact trivial

open Classical in
theorem mapToUnitsPow₀_symm_prod_fundSystem_rpow (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    (mapToUnitsPow₀ K).symm (fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ c i) = c := by
  ext
  simp_rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, Function.comp_apply,
    mapToUnitsPow₀_aux_symm_apply, EquivLike.coe_coe, Basis.equivFun_apply, Basis.repr_reindex,
    Real.log_prod _ _ (fun _ _ ↦ (Real.rpow_pos_of_pos (Units.pos_at_place _ _) _).ne'),
    Real.log_rpow (Units.pos_at_place _ _), mul_sum, mul_left_comm, ← logEmbedding_component,
    logEmbedding_fundSystem, ← sum_fn, _root_.map_sum, ← smul_eq_mul, ← Pi.smul_def,
    _root_.map_smul, Finsupp.mapDomain_equiv_apply, sum_apply', Finsupp.coe_smul, Pi.smul_apply,
    Basis.ofZLatticeBasis_repr_apply, Basis.repr_self, smul_eq_mul, Finsupp.single_apply,
    Int.cast_ite, mul_ite, Int.cast_zero, mul_zero, EmbeddingLike.apply_eq_iff_eq, sum_ite_eq',
    mem_univ, if_true, Int.cast_one, mul_one]

open Classical in
theorem mapToUnitsPow₀_apply (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c = fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ c i := by
  refine (PartialEquiv.eq_symm_apply _ (by trivial) ?_).mp
    (mapToUnitsPow₀_symm_prod_fundSystem_rpow c).symm
  rw [mapToUnitsPow₀_target]
  refine ⟨?_, norm_realToMixed_prod_units_rpow c _⟩
  exact fun _ ↦ Finset.prod_pos fun _ _ ↦ Real.rpow_pos_of_pos (Units.pos_at_place _ _) _

open Classical in
theorem mapToUnitsPow₀_symm_apply_of_norm_one {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    (mapToUnitsPow₀ K).symm x = (((basisUnitLattice K).ofZLatticeBasis ℝ).reindex
      equivFinRank).equivFun (logMap (realToMixed x)) := by
  simp_rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, EquivLike.coe_coe, Function.comp_apply]
  congr with x
  rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
    normAtPlace_realToMixed, Real.norm_eq_abs, Real.log_abs]

variable (K) in
open Classical in
theorem continuous_mapToUnitsPow₀ :
    Continuous (mapToUnitsPow₀ K) := (continuous_mapToUnitsPow₀_aux K).comp <|
  LinearEquiv.continuous_symm _ (continuous_equivFun_basis _)

open Classical in
/-- DOCSTRING -/
abbrev mapToUnitsPow_single (c : realSpace K) : InfinitePlace K → (realSpace K) :=
  fun i ↦ if hi : i = w₀ then fun _ ↦ |c w₀| else
    fun w ↦ (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ (c i)

open Classical in
theorem mapToUnitsPow₀_eq_prod_single (c : realSpace K) (w : InfinitePlace K) :
    mapToUnitsPow₀ K (fun w ↦ c w.val) w =
      ∏ i ∈ univ.erase w₀, mapToUnitsPow_single c i w := by
  rw [mapToUnitsPow₀_apply, Finset.prod_subtype (Finset.univ.erase w₀)
    (fun w ↦ (by aesop : w ∈ univ.erase w₀ ↔ w ≠ w₀))]
  exact Finset.prod_congr rfl fun w _ ↦ by rw [mapToUnitsPow_single, dif_neg w.prop]

theorem prod_mapToUnitsPow_single (c : realSpace K) :
    ∏ i, mapToUnitsPow_single c i = |c w₀| • mapToUnitsPow₀ K (fun w ↦ c w.val) := by
  classical
  ext
  rw [Pi.smul_apply, mapToUnitsPow₀_eq_prod_single, ← Finset.univ.mul_prod_erase _
    (Finset.mem_univ w₀), mapToUnitsPow_single, dif_pos rfl, smul_eq_mul, Pi.mul_apply, prod_apply]

variable (K) in
open Classical in
/-- DOCSTRING -/
@[simps source target]
def mapToUnitsPow : PartialHomeomorph (realSpace K) (realSpace K) where
  toFun c := ∏ i, mapToUnitsPow_single c i
  invFun x w :=
    if hw : w = w₀ then mixedEmbedding.norm (realToMixed x) ^ (finrank ℚ K : ℝ)⁻¹ else
      (((basisUnitLattice K).ofZLatticeBasis ℝ).reindex
        equivFinRank).equivFun (logMap (realToMixed x)) ⟨w, hw⟩
  source := {x | 0 < x w₀}
  target := {x | ∀ w, 0 < x w}
  map_source' _ h _ := by
    simp_rw [prod_mapToUnitsPow_single, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (abs_pos.mpr h.ne') (mapToUnitsPow₀_pos _ _)
  map_target' x hx := by
    refine Set.mem_setOf.mpr ?_
    dsimp only
    rw [dif_pos rfl]
    exact Real.rpow_pos_of_pos (pos_norm_realToMixed (fun w ↦ (hx w).ne')) _
  left_inv' _ h := by
    dsimp only
    ext w
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, prod_mapToUnitsPow_single, map_smul, mixedEmbedding.norm_smul,
        norm_mapToUnitsPow₀, mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (finrank_pos).ne'), Real.rpow_one, abs_of_nonneg
          (abs_nonneg _), abs_of_pos (by convert h)]
    · rw [dif_neg hw, prod_mapToUnitsPow_single, map_smul, logMap_real_smul
        (by rw [norm_mapToUnitsPow₀]; exact one_ne_zero) (abs_ne_zero.mpr (ne_of_gt h)),
        ← mapToUnitsPow₀_symm_apply_of_norm_one, PartialEquiv.left_inv _
        (by rw [mapToUnitsPow₀_source]; trivial)]
      rw [mapToUnitsPow₀_apply]
      exact norm_realToMixed_prod_units_rpow _ _
  right_inv' x hx := by
    have h₀ : mixedEmbedding.norm
        (realToMixed (mixedEmbedding.norm (realToMixed x) ^ (- (finrank ℚ K : ℝ)⁻¹) • x)) = 1 := by
      rw [map_smul, norm_smul, ← abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul, neg_mul,
        inv_mul_cancel₀, Real.rpow_neg_one, abs_of_nonneg, inv_mul_cancel₀]
      · rw [mixedEmbedding.norm_ne_zero_iff]
        intro w
        rw [normAtPlace_realToMixed, Real.norm_eq_abs, abs_ne_zero]
        exact (hx w).ne'
      refine inv_nonneg.mpr (mixedEmbedding.norm_nonneg _)
      rw [Nat.cast_ne_zero]
      exact finrank_pos.ne'
      exact mixedEmbedding.norm_nonneg _
    have hx' : ∀ w, x w ≠ 0 := fun w ↦ (hx w).ne'
    dsimp only
    rw [prod_mapToUnitsPow_single, dif_pos rfl]
    conv_lhs =>
      enter [2, 2, w]
      rw [dif_neg w.prop]
    ext w
    rw [Pi.smul_apply, ← logMap_real_smul]
    rw [← _root_.map_smul]
    rw [← mapToUnitsPow₀_symm_apply_of_norm_one h₀]
    rw [PartialEquiv.right_inv, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [abs_of_nonneg, Real.rpow_neg, mul_inv_cancel_left₀]
    · refine Real.rpow_ne_zero_of_pos ?_ _
      exact pos_norm_realToMixed hx'
    · exact mixedEmbedding.norm_nonneg (realToMixed x)
    · refine Real.rpow_nonneg ?_ _
      exact mixedEmbedding.norm_nonneg (realToMixed x)
    · rw [mapToUnitsPow₀_target]
      refine ⟨fun w ↦ ?_, h₀⟩
      exact mul_pos (Real.rpow_pos_of_pos (pos_norm_realToMixed hx') _) (hx w)
    · exact ne_of_gt (pos_norm_realToMixed hx')
    · refine Real.rpow_ne_zero_of_pos ?_ _
      exact pos_norm_realToMixed hx'
  open_source := isOpen_lt continuous_const (continuous_apply w₀)
  open_target := by
    convert_to IsOpen (⋂ w, {x : InfinitePlace K → ℝ | 0 < x w})
    · ext; simp
    · exact isOpen_iInter_of_finite fun w ↦ isOpen_lt continuous_const (continuous_apply w)
  continuousOn_toFun := by
    simp_rw [prod_mapToUnitsPow_single]
    exact ContinuousOn.smul (by fun_prop) <|
      (continuous_mapToUnitsPow₀ K).comp_continuousOn' (by fun_prop)
  continuousOn_invFun := by
    simp only
    rw [continuousOn_pi]
    intro w
    by_cases hw : w = w₀
    · simp_rw [hw, dite_true]
      refine Continuous.continuousOn ?_
      refine Continuous.rpow_const ?_ ?_
      · refine Continuous.comp' ?_ ?_
        exact mixedEmbedding.continuous_norm K
        exact ContinuousLinearMap.continuous realToMixed
      · intro _
        right
        rw [inv_nonneg]
        exact Nat.cast_nonneg' (finrank ℚ K)
    · simp_rw [dif_neg hw]
      refine Continuous.comp_continuousOn' (continuous_apply _) <|
        (continuous_equivFun_basis _).comp_continuousOn' ?_
      refine ContinuousOn.comp'' (continuousOn_logMap K) ?_ ?_
      refine Continuous.continuousOn ?_
      exact ContinuousLinearMap.continuous realToMixed
      intro x hx
      refine ne_of_gt ?_
      exact pos_norm_realToMixed (fun w ↦ (hx w).ne')

variable (K) in
theorem measurable_mapToUnitsPow_symm :
    Measurable (mapToUnitsPow K).symm := by
  classical
  dsimp [mapToUnitsPow, PartialHomeomorph.mk_coe_symm, PartialEquiv.coe_symm_mk]
  refine measurable_pi_iff.mpr fun _ ↦ ?_
  split_ifs
  · refine Measurable.pow_const ?_ _
    exact Measurable.comp' (mixedEmbedding.continuous_norm K).measurable realToMixed.measurable
  · exact Measurable.eval <|
      (continuous_equivFun_basis ((Basis.ofZLatticeBasis ℝ (unitLattice K)
        (basisUnitLattice K)).reindex equivFinRank)).measurable.comp'
        ((measurable_logMap _).comp' realToMixed.measurable)

theorem mapToUnitsPow_apply (c : realSpace K) :
    mapToUnitsPow K c = ∏ i, mapToUnitsPow_single c i := rfl

theorem mapToUnitsPow_apply' (c : realSpace K) :
    mapToUnitsPow K c = |c w₀| • mapToUnitsPow₀ K (fun w ↦ c w.val) := by
  rw [mapToUnitsPow_apply, prod_mapToUnitsPow_single]

theorem mapToUnitsPow_nonneg (c : realSpace K) (w : InfinitePlace K) :
    0 ≤ mapToUnitsPow K c w := by
  rw [mapToUnitsPow_apply']
  exact mul_nonneg (abs_nonneg _) (mapToUnitsPow₀_pos _ _).le

theorem mapToUnitsPow_zero_iff {c : realSpace K} :
    mapToUnitsPow K c = 0 ↔ c w₀ = 0 := by
  rw [mapToUnitsPow_apply', smul_eq_zero, abs_eq_zero, or_iff_left]
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  refine Function.ne_iff.mpr ⟨w, ?_⟩
  convert (mapToUnitsPow₀_pos (fun i ↦ c i) w).ne'

theorem mapToUnitsPow_zero_iff' {c : InfinitePlace K → ℝ} {w : InfinitePlace K} :
    mapToUnitsPow K c w = 0 ↔ c w₀ = 0 := by
  rw [mapToUnitsPow_apply', Pi.smul_apply, smul_eq_mul, mul_eq_zero, abs_eq_zero,
    or_iff_left (ne_of_gt (mapToUnitsPow₀_pos _ _))]

theorem mapToUnitsPow_pos {c : InfinitePlace K → ℝ} (hc : c w₀ ≠ 0) (w : InfinitePlace K) :
    0 < mapToUnitsPow K c w :=
  lt_of_le_of_ne' (mapToUnitsPow_nonneg c w) (mapToUnitsPow_zero_iff'.not.mpr hc)

open ContinuousLinearMap

/-- DOCSTRING -/
abbrev mapToUnitsPow_fDeriv_single (c : realSpace K) (i w : InfinitePlace K) :
    (realSpace K) →L[ℝ] ℝ := by
  classical
  exact if hi : i = w₀ then proj w₀ else
    (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩)) ^ c i *
      (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log) • proj i

theorem hasFDeriv_mapToUnitsPow_single (c : realSpace K) (i w : InfinitePlace K)
    (hc : 0 ≤ c w₀) :
    HasFDerivWithinAt (fun x ↦ mapToUnitsPow_single x i w)
      (mapToUnitsPow_fDeriv_single c i w) {x | 0 ≤ x w₀} c := by
  unfold mapToUnitsPow_single mapToUnitsPow_fDeriv_single
  split_ifs
  · refine HasFDerivWithinAt.congr' (hasFDerivWithinAt_apply w₀ c _) ?_ hc
    exact fun _ h ↦ by simp_rw [abs_of_nonneg (Set.mem_setOf.mp h)]
  · exact HasFDerivWithinAt.const_rpow (hasFDerivWithinAt_apply i c _) <| pos_iff.mpr (by aesop)

open Classical in
/-- DOCSTRING -/
abbrev mapToUnitsPow_jacobianCoeff (w i : InfinitePlace K) : (realSpace K) → ℝ :=
  fun c ↦ if hi : i = w₀ then 1 else |c w₀| * (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log

/-- DOCSTRING -/
abbrev mapToUnitsPow_jacobian (c : realSpace K) : (realSpace K) →L[ℝ] InfinitePlace K → ℝ :=
  pi fun i ↦ (mapToUnitsPow₀ K (fun w ↦ c w) i •
    ∑ w, (mapToUnitsPow_jacobianCoeff i w c) • proj w)

theorem hasFDeriv_mapToUnitsPow (c : InfinitePlace K → ℝ) (hc : 0 ≤ c w₀) :
    HasFDerivWithinAt (mapToUnitsPow K) (mapToUnitsPow_jacobian c) {x | 0 ≤ x w₀} c := by
  classical
  refine hasFDerivWithinAt_pi'.mpr fun w ↦ ?_
  simp_rw [mapToUnitsPow_apply, Finset.prod_apply]
  convert HasFDerivWithinAt.finset_prod fun i _ ↦ hasFDeriv_mapToUnitsPow_single c i w hc
  rw [ContinuousLinearMap.proj_pi, Finset.smul_sum]
  refine Fintype.sum_congr _ _ fun i ↦ ?_
  by_cases hi : i = w₀
  · simp_rw [hi, mapToUnitsPow_jacobianCoeff, dite_true, one_smul, dif_pos,
      mapToUnitsPow₀_eq_prod_single]
  · rw [mapToUnitsPow₀_eq_prod_single, mapToUnitsPow_jacobianCoeff, dif_neg hi, smul_smul,
      ← mul_assoc, show |c w₀| = mapToUnitsPow_single c w₀ w by simp_rw [dif_pos rfl],
      Finset.prod_erase_mul _ _ (Finset.mem_univ w₀), mapToUnitsPow_fDeriv_single, dif_neg hi,
      smul_smul,  ← mul_assoc, show w (algebraMap (𝓞 K) K
        (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ c i = mapToUnitsPow_single c i w by
      simp_rw [dif_neg hi], Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

open Classical in
theorem prod_mapToUnitsPow₀(c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    ∏ w : InfinitePlace K, mapToUnitsPow₀ K c w =
      (∏ w : {w : InfinitePlace K // IsComplex w}, mapToUnitsPow₀ K c w)⁻¹ := by
  have : ∏ w : { w  // IsComplex w}, (mapToUnitsPow₀ K) c w.val ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ ↦ ne_of_gt (mapToUnitsPow₀_pos c w)
  rw [← mul_eq_one_iff_eq_inv₀ this]
  convert norm_mapToUnitsPow₀ c
  simp_rw [norm_realToMixed, ← Fintype.prod_subtype_mul_prod_subtype (fun w ↦ IsReal w)]
  rw [← (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex)).prod_comp]
  simp_rw [Equiv.subtypeEquivRight_apply_coe]
  rw [mul_assoc, ← sq, ← Finset.prod_pow]
  congr with w
  · rw [Real.norm_eq_abs, abs_of_pos (mapToUnitsPow₀_pos c _), mult, if_pos w.prop, pow_one]
  · rw [Real.norm_eq_abs, abs_of_pos (mapToUnitsPow₀_pos c _), mult, if_neg w.prop]

open Classical in
theorem mapToUnitsPow_jacobian_det {c : realSpace K} (hc : 0 ≤ c w₀) :
    |(mapToUnitsPow_jacobian c).det| =
      (∏ w : {w : InfinitePlace K // w.IsComplex }, mapToUnitsPow₀ K (fun w ↦ c w) w)⁻¹ *
        2⁻¹ ^ NrComplexPlaces K * |c w₀| ^ (rank K) * (finrank ℚ K) * regulator K := by
  have : LinearMap.toMatrix' (mapToUnitsPow_jacobian c).toLinearMap =
      Matrix.of fun w i ↦ mapToUnitsPow₀ K (fun w ↦ c w) w *
        mapToUnitsPow_jacobianCoeff w i c := by
    ext
    simp_rw [mapToUnitsPow_jacobian, ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_smul,
      ContinuousLinearMap.coe_sum, LinearMap.toMatrix'_apply, LinearMap.pi_apply,
      LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', this]
  rw [Matrix.det_mul_column, prod_mapToUnitsPow₀, ← Matrix.det_transpose]
  simp_rw [mapToUnitsPow_jacobianCoeff]
  rw [mul_assoc, finrank_mul_regulator_eq_det K w₀ equivFinRank.symm]
  have : |c w₀| ^ rank K = |∏ w : InfinitePlace K, if w = w₀ then 1 else c w₀| := by
    rw [Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul, abs_pow]
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, rank]
  rw [this, mul_assoc, ← abs_mul, ← Matrix.det_mul_column]
  have : (2 : ℝ)⁻¹ ^ NrComplexPlaces K = |∏ w : InfinitePlace K, (mult w : ℝ)⁻¹| := by
    rw [Finset.abs_prod]
    simp_rw [mult, Nat.cast_ite, Nat.cast_one, Nat.cast_ofNat, apply_ite, abs_inv, abs_one, inv_one,
      Nat.abs_ofNat, Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
    rw [Finset.filter_not, Finset.card_univ_diff, ← Fintype.card_subtype]
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, ← NrRealPlaces, add_tsub_cancel_left]
  rw [this, mul_assoc, ← abs_mul, ← Matrix.det_mul_row, abs_mul]
  congr
  · rw [abs_eq_self.mpr]
    rw [inv_nonneg]
    exact Finset.prod_nonneg fun _ _ ↦ (mapToUnitsPow₀_pos _ _).le
  · ext
    simp only [Matrix.transpose_apply, Matrix.of_apply, ite_mul, one_mul, mul_ite]
    split_ifs
    · rw [inv_mul_cancel₀ mult_coe_ne_zero]
    · rw [← mul_assoc, mul_comm _ (c w₀), mul_assoc, inv_mul_cancel_left₀ mult_coe_ne_zero,
        abs_eq_self.mpr hc]

open MeasureTheory

private theorem setLIntegral_mapToUnitsPow_aux₀ {s : Set (realSpace K)} (hs : s ⊆ {x | 0 ≤ x w₀}) :
    s \ (s ∩ {x | 0 < x w₀}) ⊆ {x | x w₀ = 0} := by
  refine fun _ h ↦ eq_of_ge_of_not_gt (hs h.1) ?_
  have := h.2
  simp_rw [Set.mem_inter_iff, not_and, h.1, true_implies] at this
  exact this

private theorem setLIntegral_mapToUnitsPow_aux₁ :
    volume {x : realSpace K | x w₀ = 0} = 0 := by
  let A : AffineSubspace ℝ (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w₀ = 0}, by aesop⟩, rfl⟩ (by aesop))
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  have : 1 ∈ A := h ▸ Set.mem_univ _
  simp [A] at this

private theorem setLIntegral_mapToUnitsPow_aux₂ {s : Set (realSpace K)} (hs : s ⊆ {x | 0 ≤ x w₀}) :
    (mapToUnitsPow K) '' s =ᵐ[volume] (mapToUnitsPow K) '' (s ∩ {x | 0 < x w₀}) := by
  refine measure_symmDiff_eq_zero_iff.mp ?_
  rw [symmDiff_of_ge (Set.image_mono Set.inter_subset_left)]
  have : mapToUnitsPow K '' s \ mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ⊆ { 0 } := by
    rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
    have hx'' : x ∉ s ∩ {x | 0 < x w₀} := fun h ↦ hx' (Set.mem_image_of_mem _ h)
    simp_rw [Set.mem_inter_iff, Set.mem_setOf_eq, not_and] at hx''
    rw [Set.mem_singleton_iff, mapToUnitsPow_zero_iff]
    refine eq_of_ge_of_not_gt (hs hx) (hx'' hx)
  exact measure_mono_null this (measure_singleton _)

open ENNReal Classical in
theorem setLIntegral_mapToUnitsPow {s : Set (realSpace K)} (hs₀ : MeasurableSet s)
    (hs₁ : s ⊆ {x | 0 ≤ x w₀}) (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (mapToUnitsPow K) '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * ENNReal.ofReal (regulator K) * (finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal |x w₀| ^ rank K *
        ENNReal.ofReal (∏ i : {w : InfinitePlace K // IsComplex w},
          (mapToUnitsPow₀ K (fun w ↦ x w) i))⁻¹ * f (mapToUnitsPow K x) := by
  rw [setLIntegral_congr (setLIntegral_mapToUnitsPow_aux₂ hs₁)]
  have : s =ᵐ[volume] (s ∩ {x | 0 < x w₀} : Set (realSpace K)) := by
    refine measure_symmDiff_eq_zero_iff.mp <|
      measure_mono_null ?_ setLIntegral_mapToUnitsPow_aux₁
    rw [symmDiff_of_ge Set.inter_subset_left]
    exact setLIntegral_mapToUnitsPow_aux₀ hs₁
  rw [setLIntegral_congr this]
  have h : MeasurableSet (s ∩ {x | 0 < x w₀}) :=
    hs₀.inter (measurableSet_lt measurable_const (measurable_pi_apply w₀))
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume h (fun c hc ↦
    HasFDerivWithinAt.mono (hasFDeriv_mapToUnitsPow c (hs₁ (Set.mem_of_mem_inter_left hc)))
    (Set.inter_subset_left.trans hs₁)) ((mapToUnitsPow K).injOn.mono Set.inter_subset_right)]
  rw [setLIntegral_congr_fun h
    (ae_of_all volume fun c hc ↦ by rw [mapToUnitsPow_jacobian_det
    (hs₁ (Set.mem_of_mem_inter_left hc))]), ← lintegral_const_mul']
  · congr with x
    -- This will be useful for positivity goals
    have : 0 ≤ (∏ w : {w : InfinitePlace K // IsComplex w}, mapToUnitsPow₀ K (fun w ↦ x w) w)⁻¹ :=
      inv_nonneg.mpr <| Finset.prod_nonneg fun w _ ↦ (mapToUnitsPow₀_pos _ _).le
    rw [ofReal_mul (by positivity), ofReal_mul (by positivity), ofReal_mul (by positivity),
      ofReal_mul (by positivity), ofReal_natCast, ofReal_pow (by positivity), ofReal_pow
      (by positivity), ofReal_inv_of_pos zero_lt_two, ofReal_ofNat]
    ring
  · exact mul_ne_top (mul_ne_top (pow_ne_top (inv_ne_top.mpr two_ne_zero)) ofReal_ne_top)
      (natCast_ne_top _)

end mapToUnitsPow

noncomputable section mapToUnitsPowComplex

variable [NumberField K]

def mapToUnitsPowComplex : PartialHomeomorph
    ((realSpace K) × ({w : InfinitePlace K // IsComplex w} → ℝ)) (mixedSpace K) :=
  PartialHomeomorph.trans
    (PartialHomeomorph.prod (mapToUnitsPow K) (PartialHomeomorph.refl _))
    (polarCoordMixedSpace K).symm

theorem mapToUnitsPowComplex_source :
    (mapToUnitsPowComplex K).source = {x | 0 < x w₀} ×ˢ Set.univ.pi fun _ ↦ Set.Ioo (-π) π := by
  ext
  simp_rw [mapToUnitsPowComplex, PartialHomeomorph.trans_source, PartialHomeomorph.prod_source,
    PartialHomeomorph.refl_source, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true,
    Set.mem_preimage, PartialHomeomorph.prod_apply, PartialHomeomorph.refl_apply, id_eq,
    PartialHomeomorph.symm_source, polarCoordMixedSpace_target, Set.mem_prod, mapToUnitsPow_source]
  rw [and_congr_right]
  intro h
  rw [and_iff_right_iff_imp]
  intro _
  simp_rw [Set.mem_univ_pi, Set.mem_ite_univ_left, not_isReal_iff_isComplex]
  intro w _
  rw [Set.mem_Ioi, lt_iff_le_and_ne]
  refine ⟨mapToUnitsPow_nonneg _ _, ?_⟩
  rw [ne_comm, ne_eq, mapToUnitsPow_zero_iff']
  exact ne_of_gt h

theorem mapToUnitsPowComplex_target :
    (mapToUnitsPowComplex K).target =
      (Set.univ.pi fun _ ↦ Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Complex.slitPlane) := by
  ext
  simp_rw [mapToUnitsPowComplex, PartialHomeomorph.trans_target, PartialHomeomorph.symm_target,
    polarCoordMixedSpace_source, PartialHomeomorph.prod_target, PartialHomeomorph.refl_target,
    Set.mem_inter_iff, Set.mem_preimage, mapToUnitsPow_target, Set.mem_prod, Set.mem_univ,
    true_and, and_true, and_comm]
  rw [and_congr_right]
  intro h
  simp_rw [PartialHomeomorph.symm_symm, polarCoordMixedSpace_apply, realProdComplexProdEquiv_apply,
    Set.mem_pi, Set.mem_univ, true_implies]
  refine ⟨?_, ?_⟩
  · intro h' w
    specialize h' w
    simp_rw [dif_pos w.prop] at h'
    exact h'
  · intro h' w
    by_cases hw : IsReal w
    · simp_rw [dif_pos hw]
      exact h' ⟨w, hw⟩
    · simp_rw [dif_neg hw]
      rw [Complex.polarCoord_apply]
      dsimp only
      rw [Set.mem_pi] at h
      specialize h ⟨w, not_isReal_iff_isComplex.mp hw⟩ (Set.mem_univ _)
      rw [AbsoluteValue.pos_iff]
      exact Complex.slitPlane_ne_zero h

variable {K}

theorem mapToUnitsPowComplex_apply (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
    mapToUnitsPowComplex K x =
      (fun w ↦ mapToUnitsPow K x.1 w.val,
        fun w ↦ Complex.polarCoord.symm (mapToUnitsPow K x.1 w.val, x.2 w)) := rfl

theorem mixedToReal_mapToUnitsPowComplex
    (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ)) :
    mixedToReal (mapToUnitsPowComplex K x) = mapToUnitsPow K x.1 := by
  ext w
  simp_rw [mapToUnitsPowComplex_apply]
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal _ ⟨w, hw⟩]
  · rw [mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, Complex.norm_eq_abs, Complex.polarCoord_symm_abs,
      abs_of_nonneg (mapToUnitsPow_nonneg x.1 w)]

theorem mapToUnitsPowComplex_image_prod (s : Set (InfinitePlace K → ℝ))
    (t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    mapToUnitsPowComplex K '' (s ×ˢ t) =
      (polarCoordMixedSpace K).symm '' (mapToUnitsPow K '' s) ×ˢ t := by
  ext
  simp_rw [mapToUnitsPowComplex, PartialHomeomorph.coe_trans, Function.comp_apply,
    PartialHomeomorph.prod_apply, PartialHomeomorph.refl_apply, id_eq,
    polarCoordMixedSpace_symm_apply, Set.mem_image, Set.mem_prod, Prod.exists]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact ⟨mapToUnitsPow K x, y, ⟨Set.mem_image_of_mem _ hx, hy⟩, rfl⟩
  · rintro ⟨_, y, ⟨⟨⟨x, hx, rfl⟩, hy⟩, rfl⟩⟩
    exact ⟨x, y, ⟨hx, hy⟩, rfl⟩

theorem mapToUnitsPowComplex_prod_indicator_aux (x y : ℝ × ℝ) (hx : x ∈ Set.Ici 0 ×ˢ Set.Icc (-π) π)
    (hy : y ∈ Complex.polarCoord.target)
    (hxy : Complex.polarCoord.symm x = Complex.polarCoord.symm y) :
    x = y := by
  suffices x ∈ Complex.polarCoord.target from Complex.polarCoord.symm.injOn this hy hxy
  suffices x.1 ≠ 0 ∧ x.2 ≠ -π ∧ x.2 ≠ π by
    simp only [Complex.polarCoord_target, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    simp at hx
    refine ⟨?_, ?_, ?_⟩
    · rw [lt_iff_le_and_ne]
      exact ⟨hx.1, this.1.symm⟩
    · rw [lt_iff_le_and_ne]
      exact ⟨hx.2.1, this.2.1.symm⟩
    · rw [lt_iff_le_and_ne]
      exact ⟨hx.2.2, this.2.2⟩
  have := (Complex.polarCoord_symm_mem_polarCoord_source x).mp ?_
  have hx₁ : 0 < x.1 := by
    refine lt_iff_le_and_ne.mpr ⟨?_, ?_⟩
    exact hx.1
    exact this.1.symm
  · refine ⟨?_, ?_, ?_⟩
    · exact this.1
    · have := this.2.1 hx₁ (-1)
      rwa [show π + (-1 : ℤ) * (2 * π) = -π by ring, ne_comm] at this
    · have := this.2.1 hx₁ 0
      rwa [Int.cast_zero, zero_mul, add_zero, ne_comm] at this
  · rw [hxy]
    exact Complex.polarCoord.map_target hy

theorem mapToUnitsPowComplex_prod_indicator
    {s : Set (InfinitePlace K → ℝ)} {t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)}
    (ht : t ⊆ Set.univ.pi fun _ ↦ Set.Icc (-π) π)
    (x : (InfinitePlace K → ℝ) × ({w // IsComplex w} → ℝ))
    (hx : x ∈ (polarCoordMixedSpace K).target) :
    (mapToUnitsPowComplex K '' s ×ˢ t).indicator (fun _ ↦ (1 : ENNReal))
      ((polarCoordMixedSpace K).symm x) =
      (mapToUnitsPow K '' s).indicator 1 x.1 * t.indicator 1 x.2 := by
  classical
  simp_rw [mapToUnitsPowComplex_image_prod, ← Set.indicator_prod_one, Prod.mk.eta,
    Set.indicator_apply, Set.mem_image, polarCoordMixedSpace_symm_apply, Prod.mk.inj_iff]
  refine if_congr ⟨fun ⟨y, hy, ⟨hxy₁, hxy₂⟩⟩ ↦ ?_, fun h ↦ ⟨x, h, rfl, rfl⟩⟩ rfl rfl
  suffices y = x by rwa [← this]
  have hxy : ∀ i (hi : IsComplex i), y.1 i = x.1 i ∧ y.2 ⟨i, hi⟩ = x.2 ⟨i, hi⟩ := by
      intro i hi
      rw [← Prod.mk.inj_iff]
      refine mapToUnitsPowComplex_prod_indicator_aux _ _ ?_ ?_ (congr_fun hxy₂ ⟨i, hi⟩)
      · rw [Set.prod_mk_mem_set_prod_eq]
        refine ⟨?_, ?_⟩
        · obtain ⟨t, _, ht⟩ := hy.1
          rw [← ht]
          exact mapToUnitsPow_nonneg _ _
        · exact ht hy.2 ⟨i, hi⟩ trivial
      · simp_rw [polarCoordMixedSpace_target, Set.mem_prod, Set.mem_univ_pi, Set.mem_ite_univ_left,
          not_isReal_iff_isComplex] at hx
        exact ⟨hx.1 i hi, hx.2 ⟨i, hi⟩⟩
  ext i
  · obtain hi | hi := isReal_or_isComplex i
    · exact congr_fun hxy₁ ⟨i, hi⟩
    · exact (hxy i hi).1
  · exact (hxy i.val i.prop).2

-- Isn't this result used already to compute the integral?
theorem mapToUnitsPow_image_minus_image_inter_aux {s : Set (InfinitePlace K → ℝ)}
    (hs : s ⊆ {x | 0 ≤ x w₀}) :
    s \ (s ∩ {x | 0 < x w₀}) ⊆ {x | x w₀ = 0} := by
  refine fun _ h ↦ eq_of_ge_of_not_gt (hs h.1) ?_
  have := h.2
  simp_rw [Set.mem_inter_iff, not_and, h.1, true_implies] at this
  exact this

theorem mapToUnitsPow_image_minus_image_inter
    {s : Set (InfinitePlace K → ℝ)} (hs : s ⊆ {x | 0 ≤ x w₀}) :
    mapToUnitsPow K '' s \ mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ⊆ {0} := by
  rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
  have hx'' : x ∉ s ∩ {x | 0 < x w₀} := fun h ↦ hx' (Set.mem_image_of_mem _ h)
  rw [Set.mem_singleton_iff, mapToUnitsPow_zero_iff]
  exact mapToUnitsPow_image_minus_image_inter_aux hs ⟨hx, hx''⟩

theorem measurable_mapToUnitsPow_image {s : Set (InfinitePlace K → ℝ)}
    (hs : MeasurableSet s) (hs' : s ⊆ {x | 0 ≤ x w₀}) :
    MeasurableSet (mapToUnitsPow K '' s) := by
  have hm : MeasurableSet (mapToUnitsPow K '' (s ∩ {x | 0 < x w₀})) := by
    rw [PartialHomeomorph.image_eq_target_inter_inv_preimage _ (fun _ h ↦ h.2)]
    refine (mapToUnitsPow K).open_target.measurableSet.inter ?_
    have : MeasurableSet (s ∩ {x | 0 < x w₀}) :=
      hs.inter (measurableSet_lt measurable_const (measurable_pi_apply w₀))
    exact MeasurableSet.preimage this (measurable_mapToUnitsPow_symm K)
  obtain h | h : mapToUnitsPow K '' s = mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ∨
      mapToUnitsPow K '' s = mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ∪ { 0 } := by
    have h₀ : mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ⊆ mapToUnitsPow K '' s :=
      Set.image_mono Set.inter_subset_left
    have h₂ : ∀ ⦃s t u : Set (realSpace K)⦄, t ⊆ s → s \ t = u → s = t ∪ u := by aesop
    obtain h₁ | h₁ := Set.subset_singleton_iff_eq.mp (mapToUnitsPow_image_minus_image_inter hs')
    · left
      rw [h₂ h₀ h₁, Set.union_empty]
    · right
      rw [h₂ h₀ h₁]
  · rwa [h]
  · rw [h]
    exact MeasurableSet.union hm (measurableSet_singleton 0)

open MeasureTheory MeasureTheory.Measure

open Classical in
theorem volume_mapToUnitsPowComplex_set_prod_set {s : Set (InfinitePlace K → ℝ)}
    (hs : MeasurableSet s) (hs' : s ⊆ {x | 0 ≤ x w₀} )
    {t : Set ({w : InfinitePlace K // IsComplex w} → ℝ)}
    (ht : MeasurableSet t) (ht' : t ⊆ Set.univ.pi fun _ ↦ Set.Icc (-π) π)
    (hm : MeasurableSet (mapToUnitsPowComplex K '' s ×ˢ t)) :
    volume (mapToUnitsPowComplex K '' (s ×ˢ t)) =
      volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) * ∫⁻ x in mapToUnitsPow K '' s,
        ∏ w : {w : InfinitePlace K // IsComplex w}, (x w).toNNReal := by
  rw [← setLIntegral_one, ← lintegral_indicator _ hm,
    lintegral_eq_lintegral_polarCoordMixedSpace_symm K _
    ((measurable_indicator_const_iff 1).mpr hm),
    setLIntegral_congr (setLIntegral_mapToUnitsPow_aux₂ hs')]
  calc
    _ = ∫⁻ x in Set.univ.pi fun w ↦ if IsReal w then Set.univ else Set.Ioi 0,
          ∫⁻ y in Set.univ.pi fun _ ↦ Set.Ioo (-π) π,
            (∏ w : {w // IsComplex w}, (x w.val).toNNReal) *
              ((mapToUnitsPow K '' s).indicator 1 x * t.indicator 1 y) := by
      rw [lintegral_lintegral, Measure.prod_restrict, ← polarCoordMixedSpace_target]
      · refine setLIntegral_congr_fun (measurableSet_polarCoordMixedSpace_target K) ?_
        filter_upwards with x hx
        simp_rw [mapToUnitsPowComplex_prod_indicator ht' x hx]
      · refine Measurable.aemeasurable ?_
        refine Measurable.mul ?_ ?_
        · exact measurable_coe_nnreal_ennreal_iff.mpr <|
            Finset.measurable_prod _ fun _ _ ↦ by fun_prop
        · refine Measurable.mul ?_ ?_
          · refine Measurable.ite ?_ ?_ ?_
            · change MeasurableSet (Prod.fst ⁻¹' (mapToUnitsPow K '' s))
              refine measurable_fst ?_
              refine measurable_mapToUnitsPow_image hs hs'
            · exact measurable_const
            · exact measurable_const
          · refine Measurable.comp' ?_ measurable_snd
            exact measurable_const.indicator ht
    _ = volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) *
          ∫⁻ x in Set.univ.pi fun w ↦ if IsReal w then Set.univ else Set.Ioi 0,
            (∏ w : {w // IsComplex w}, (x w.val).toNNReal) *
              (mapToUnitsPow K '' s).indicator 1 x := by
      conv_lhs =>
        enter [2, x]
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
        rw [lintegral_const_mul' _ _ (by
            rw [Set.indicator_apply]
            split_ifs
            exacts [ENNReal.one_ne_top, ENNReal.zero_ne_top])]
        rw [← lintegral_indicator _ (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo),
          Set.indicator_indicator, lintegral_indicator_one ((MeasurableSet.univ_pi
          fun _ ↦ measurableSet_Ioo).inter ht)]
      rw [← lintegral_const_mul']
      · congr with x
        ring
      · refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)
        simp_rw [volume_pi, pi_pi, Real.volume_Ioo, Finset.prod_const]
        refine ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    _ = volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) *
          ∫⁻ x in Set.univ.pi fun w ↦ if IsReal w then Set.univ else Set.Ioi 0,
            (∏ w : {w // IsComplex w}, (x w.val).toNNReal) *
              (mapToUnitsPow K '' (s ∩ {x | 0 < x w₀})).indicator 1 x := by
      congr 1
      refine lintegral_congr_ae ?_
      refine Filter.EventuallyEq.mul ?_ ?_
      · exact Filter.EventuallyEq.rfl
      · refine indicator_ae_eq_of_ae_eq_set ?_
        refine Filter.EventuallyEq.restrict ?_
        exact setLIntegral_mapToUnitsPow_aux₂ hs'
    _ = volume ((Set.univ.pi fun _ ↦ Set.Ioo (-π) π) ∩ t) *
          ∫⁻ x in mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}),
            ∏ w : {w // IsComplex w}, (x w.val).toNNReal := by
      rw [← lintegral_indicator, ← lintegral_indicator]
      congr with x
      rw [Set.indicator_mul_right, Set.indicator_indicator, Set.inter_eq_right.mpr]
      by_cases hx : x ∈ (mapToUnitsPow K) '' (s ∩ {x | 0 < x w₀})
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one,
          ENNReal.coe_finset_prod]
      · rw [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem hx, mul_zero]
      · rintro _ ⟨x, hx, rfl⟩
        refine Set.mem_univ_pi.mpr fun _ ↦ ?_
        rw [Set.mem_ite_univ_left]
        intro _
        rw [Set.mem_Ioi]
        exact mapToUnitsPow_pos (ne_of_gt hx.2) _
      · refine measurable_mapToUnitsPow_image ?_ ?_
        · exact hs.inter (measurableSet_lt measurable_const (measurable_pi_apply w₀))
        · exact Set.inter_subset_left.trans hs'
      · refine MeasurableSet.univ_pi fun _ ↦ ?_
        refine MeasurableSet.ite' (fun _ ↦ ?_) (fun _ ↦ ?_)
        exact MeasurableSet.univ
        exact measurableSet_Ioi

end mapToUnitsPowComplex

namespace fundamentalCone

open Pointwise FiniteDimensional

variable [NumberField K]

/-- DOCSTRING -/
abbrev normLessThanOne : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

/-- DOCSTRING -/
abbrev normEqOne : Set (mixedSpace K) := {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x = 1}

variable {K}

theorem mem_normEqOne_of_normAtPlace_eq {x y : mixedSpace K} (hx : x ∈ normEqOne K)
    (hy : ∀ w, normAtPlace w y = normAtPlace w x) :
    y ∈ normEqOne K := by
  have h₁ : mixedEmbedding.norm y = mixedEmbedding.norm x := by
    simp_rw [mixedEmbedding.norm_apply, hy]
  exact ⟨mem_of_normAtPlace_eq hx.1 hy, h₁ ▸ hx.2⟩

theorem smul_normEqOne {c : ℝ} (hc : 0 < c) :
    c • normEqOne K = {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x = c ^ finrank ℚ K} := by
  ext
  rw [← Set.preimage_smul_inv₀ (ne_of_gt hc), Set.preimage_setOf_eq, Set.mem_setOf_eq,
    mixedEmbedding.norm_smul, abs_inv, abs_eq_self.mpr hc.le, inv_pow, mul_comm, mul_inv_eq_one₀
    (pow_ne_zero _ (ne_of_gt hc)), Set.mem_setOf_eq, and_congr_left_iff]
  exact fun _ ↦ smul_mem_iff_mem (inv_ne_zero (ne_of_gt hc))

theorem exists_mem_smul_normEqOne {x : mixedSpace K} (hx : x ∈ normLessThanOne K) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ x ∈ c • normEqOne K := by
  have h₁ : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
  have h₂ : 0 < mixedEmbedding.norm x ^ (finrank ℚ K : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (norm_pos_of_mem hx.1) _
  refine ⟨(mixedEmbedding.norm x) ^ (finrank ℚ K : ℝ)⁻¹, h₂, ?_, ?_⟩
  · exact Real.rpow_le_one (mixedEmbedding.norm_nonneg _) hx.2 (inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [smul_normEqOne h₂]
    refine ⟨hx.1, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (mixedEmbedding.norm_nonneg _), inv_mul_cancel₀ h₁,
      Real.rpow_one]

theorem smul_normEqOne_subset {c : ℝ} (hc₁ : 0 < c) (hc₂ : c ≤ 1) :
    c • normEqOne K ⊆ normLessThanOne K := by
  rw [smul_normEqOne hc₁]
  refine fun x hx ↦ ⟨hx.1, ?_⟩
  rw [hx.2]
  exact pow_le_one _ hc₁.le hc₂

theorem normLessThanOne_eq_union_smul_normEqOne :
    normLessThanOne K = ⋃ c ∈ Set.Ioc (0 : ℝ) 1, c • normEqOne K := by
  ext
  simp_rw [Set.mem_iUnion, Set.mem_Ioc, exists_prop, and_assoc]
  exact ⟨fun hx ↦ exists_mem_smul_normEqOne hx,
    fun ⟨_, h₁, h₂, hx⟩ ↦ smul_normEqOne_subset h₁ h₂ hx⟩

theorem measurableSet_normLessThanOne :
    MeasurableSet (normLessThanOne K) :=
  -- MeasurableSet.inter (measurableSet K) <|
  --   measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const
  sorry

theorem isBounded_normLessThanOne :
    IsBounded (normLessThanOne K) := by
  sorry

variable (K) in
open Classical in
abbrev box₁ : Set (realSpace K) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Ioc 0 1 else Set.Ico 0 1

theorem mem_Ioc_of_mem_box₁ {c : realSpace K} (hc : c ∈ box₁ K) :
    c w₀ ∈ Set.Ioc 0 1 := by
  have := hc w₀ (Set.mem_univ _)
  simp_rw [ite_true] at this
  exact this

theorem mem_Ico_of_mem_box₁ {c : realSpace K} (hc : c ∈ box₁ K) {w : InfinitePlace K}
    (hw : w ≠ w₀) :
    c w ∈ Set.Ico 0 1 := by
  have := hc w (Set.mem_univ _)
  simp_rw [if_neg hw] at this
  exact this

theorem mixedToReal_normEqOne :
    mixedToReal '' (normEqOne K ∩ {x | ∀ w, 0 < x.1 w}) =
      mapToUnitsPow₀ K '' (Set.univ.pi fun _ ↦ Set.Ico 0 1) := by
  classical
  ext
  simp_rw [Set.mem_image, normEqOne, Set.mem_inter_iff, fundamentalCone,
    Set.mem_diff, Set.mem_preimage, ZSpan.mem_fundamentalDomain]
  constructor
  · rintro ⟨x, ⟨⟨⟨h₁⟩, h₂⟩, h₃⟩, rfl⟩
    refine ⟨(mapToUnitsPow₀ K).symm (mixedToReal x), ?_, ?_⟩
    · intro i _
      rw [mapToUnitsPow₀_symm_apply_of_norm_one (by rwa [norm_mixedToRealToMixed]),
        logMap_mixedToRealToMixed_of_norm_one h₂]
      exact h₁ (equivFinRank.symm i)
    · rw [PartialEquiv.right_inv]
      exact mixedToReal_mem_target h₃ h₂
  · rintro ⟨c, hc, rfl⟩
    refine ⟨realToMixed (mapToUnitsPow₀ K c), ⟨⟨⟨fun i ↦ ?_, ?_⟩,
      norm_mapToUnitsPow₀ c⟩, fun w ↦ mapToUnitsPow₀_pos c _⟩,
      realToMixedToReal_eq_self_of_nonneg fun w _ ↦ ( mapToUnitsPow₀_pos c w).le⟩
    · rw [show i = equivFinRank.symm (equivFinRank i) by rw [Equiv.symm_apply_apply],
        ← Basis.repr_reindex_apply, ← Basis.equivFun_apply, ← mapToUnitsPow₀_symm_apply_of_norm_one
        (norm_mapToUnitsPow₀ c), PartialEquiv.left_inv _ (by trivial)]
      exact hc _ trivial
    · rw [Set.mem_setOf_eq, norm_mapToUnitsPow₀]
      exact one_ne_zero

omit [NumberField K] in
private theorem mixedToReal_normLessThanOne_aux₀ {c : ℝ} (hc : 0 < c) :
    {x : mixedSpace K | ∀ w, 0 < x.1 w} = c •  {x | ∀ w, 0 < x.1 w} := by
  ext x
  refine ⟨fun hx ↦
    ⟨c⁻¹ • x, fun w ↦ mul_pos (inv_pos.mpr hc) (hx w), by simp_rw [smul_inv_smul₀ hc.ne']⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact fun w ↦ mul_pos hc (hy w)

private theorem mixedToReal_normLessThanOne_aux₁ {c : ℝ} (hc : 0 < c) :
    mixedToReal '' (c • normEqOne K ∩ {x | ∀ w, 0 < x.1 w}) =
      c • mixedToReal '' (normEqOne K ∩ {x | ∀ w, 0 < x.1 w}) := by
  nth_rewrite 1 [mixedToReal_normLessThanOne_aux₀ hc, ← Set.smul_set_inter₀ hc.ne']
  ext
  constructor
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    refine ⟨c⁻¹ • mixedToReal x, ⟨c⁻¹ • x, ?_, ?_⟩, ?_⟩
    · rwa [← Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    · rw [mixedToReal_smul _ (inv_nonneg.mpr hc.le)]
    · simp_rw [smul_inv_smul₀ hc.ne']
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨c • x, Set.smul_mem_smul_set hx, by rw [mixedToReal_smul _ hc.le]⟩

theorem mixedToReal_normLessThanOne :
    mixedToReal '' (normLessThanOne K ∩ {x | ∀ w, 0 < x.1 w}) = mapToUnitsPow K '' (box₁ K) := by
  classical
  rw [normLessThanOne_eq_union_smul_normEqOne, Set.iUnion₂_inter, Set.image_iUnion₂,
    Set.iUnion₂_congr (fun _ h ↦ by rw [mixedToReal_normLessThanOne_aux₁ h.1]),
    mixedToReal_normEqOne]
  ext
  simp_rw [Set.mem_iUnion, Set.mem_image, exists_prop', nonempty_prop, Set.mem_smul_set]
  constructor
  · rintro ⟨n, hn, ⟨x, ⟨c, hc, rfl⟩, rfl⟩⟩
    refine ⟨fun w ↦ if hw : w = w₀ then n else c ⟨w, hw⟩, ?_, ?_⟩
    · refine Set.mem_univ_pi.mpr ?_
      intro w
      by_cases hw : w = w₀
      · rw [hw, dif_pos rfl, if_pos rfl]
        exact hn
      · rw [dif_neg hw, if_neg hw]
        exact hc ⟨w, hw⟩ trivial
    · rw [mapToUnitsPow_apply', dif_pos rfl, abs_of_pos hn.1]
      conv_lhs =>
        enter [2, 2, w]
        rw [dif_neg w.prop]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c w₀, mem_Ioc_of_mem_box₁ hc, mapToUnitsPow₀ K fun w ↦ c w, ⟨fun w ↦ c w,
      fun w _ ↦ mem_Ico_of_mem_box₁ hc w.prop, rfl⟩, ?_⟩
    rw [mapToUnitsPow_apply', abs_of_pos (mem_Ioc_of_mem_box₁ hc).1]

open MeasureTheory

open Classical in
theorem volume_normLessThanOne :
    volume (normLessThanOne K) =
      2 ^ NrRealPlaces K * NNReal.pi ^ NrComplexPlaces K * (regulator K).toNNReal := by
  sorry

open Classical in
theorem volume_frontier_normLessThanOne :
    volume (frontier (normLessThanOne K)) = 0 := by
  sorry


end NumberField.mixedEmbedding.fundamentalCone
