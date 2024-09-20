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

namespace NumberField.mixedEmbedding

noncomputable section realSpace

abbrev realSpace := InfinitePlace K → ℝ

variable {K}

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
def mixedToReal (x : mixedSpace K) : realSpace K :=
    fun w ↦ if hw : IsReal w then x.1 ⟨w, hw⟩ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖

@[simp]
theorem mixedToReal_apply_of_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    mixedToReal x w.val = x.1 w := by
  rw [mixedToReal, dif_pos]

theorem mixedToReal_apply_of_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    mixedToReal x w.val = ‖x.2 w‖ := by
  rw [mixedToReal, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]

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
  · rw [mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, realToMixed_apply_of_isComplex _ hw,
    if_neg (not_isReal_iff_isComplex.mpr hw), Complex.norm_real]

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

@[simp]
theorem norm_mixedToReal (x : mixedSpace K) (w : InfinitePlace K) :
    ‖mixedToReal x w‖ = normAtPlace w x := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal _ ⟨w, hw⟩, normAtPlace_apply_isReal]
  · rw [mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, normAtPlace_apply_isComplex, norm_norm]

@[simp]
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
@[simp]
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

open scoped Real

open Classical in
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

def polarCoordMixedSpace : PartialHomeomorph
    (mixedSpace K) ((realSpace K) × ({w : InfinitePlace K // IsComplex w} → ℝ)) :=
  ((PartialHomeomorph.refl _).prod
    (PartialHomeomorph.pi fun _ ↦ Complex.polarCoord)).transHomeomorph (realProdComplexProdEquiv K)

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

open FiniteDimensional Finset NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

open Classical in
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

variable {K}

theorem mapToUnitsPow₀_aux_symm_apply (x : InfinitePlace K → ℝ) :
    (mapToUnitsPow₀_aux K).symm x = fun w ↦ w.val.mult * Real.log (x w.val) := rfl

def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

variable (K)

open Classical in
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
  rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, EquivLike.coe_coe, Function.comp_apply]
  congr with x
  rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
    normAtPlace_realToMixed, Real.norm_eq_abs, Real.log_abs]

open Classical in
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
  sorry

variable (K)

open Classical in
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
    dsimp only
    rw [prod_mapToUnitsPow_single, dif_pos rfl]
    conv_lhs =>
      enter [2, 2, w]
      rw [dif_neg w.prop]
    ext w
    rw [Pi.smul_apply, ← logMap_real_smul]
    rw [← _root_.map_smul]
    rw [← mapToUnitsPow₀_symm_apply K h₀]
    rw [PartialEquiv.right_inv, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [abs_of_nonneg, Real.rpow_neg, mul_inv_cancel_left₀]
    · refine Real.rpow_ne_zero_of_pos ?_ _
      exact pos_norm_realToMixed hx
    · exact mixedEmbedding.norm_nonneg (realToMixed x)
    · refine Real.rpow_nonneg ?_ _
      exact mixedEmbedding.norm_nonneg (realToMixed x)
    · rw [mapToUnitsPow₀_target]
      refine ⟨fun w ↦ ?_, h₀⟩
      exact mul_pos (Real.rpow_pos_of_pos (pos_norm_realToMixed hx) _) (hx w)
    · exact ne_of_gt (pos_norm_realToMixed hx)
    · refine Real.rpow_ne_zero_of_pos ?_ _
      exact pos_norm_realToMixed hx
#exit
  open_source := isOpen_lt continuous_const (continuous_apply w₀)
  open_target := by
    convert_to IsOpen (⋂ w, {x : InfinitePlace K → ℝ | 0 < x w})
    · ext; simp
    · exact isOpen_iInter_of_finite fun w ↦ isOpen_lt continuous_const (continuous_apply w)
  continuousOn_toFun := ContinuousOn.smul (by fun_prop) <|
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
      refine ContinuousOn.comp'' (continuousOn_logMap) ?_ ?_
      refine Continuous.continuousOn ?_
      exact ContinuousLinearMap.continuous realToMixed
      intro x hx
      refine ne_of_gt ?_
      exact pos_norm_realToMixed hx

end mapToUnitsPow

namespace fundamentalCone

variable [NumberField K]

abbrev normLessThanOne : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

theorem measurableSet_normLessThanOne :
    MeasurableSet (normLessThanOne K) :=
  -- MeasurableSet.inter (measurableSet K) <|
  --   measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const
  sorry

theorem isBounded_normLessThanOne :
    IsBounded (normLessThanOne K) := by
  sorry

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
