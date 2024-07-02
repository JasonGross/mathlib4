import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory MeasureTheory.Measure

theorem MeasureTheory.measure_restrict_pi_pi {ι : Type*} {α : ι → Type*} [Fintype ι]
    [(i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))
    [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) :
    (Measure.pi μ).restrict (Set.univ.pi fun i ↦ s i) =
      Measure.pi (fun i ↦ (μ i).restrict (s i)) := by
  refine (Measure.pi_eq fun _ h ↦ ?_).symm
  simp_rw [restrict_apply (MeasurableSet.univ_pi h), restrict_apply (h _),
    ← Set.pi_inter_distrib, pi_pi]

theorem MeasureTheory.Measure.restrict_prod_eq_univ_prod {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite ν] [MeasureTheory.SFinite μ]  (t : Set β) :
    μ.prod (ν.restrict t) = (μ.prod ν).restrict (Set.univ ×ˢ t) := by
  have : μ = μ.restrict Set.univ := Measure.restrict_univ.symm
  rw [this, Measure.prod_restrict, ← this]

theorem measurePreserving_pi {ι : Type*} [Fintype ι] {α β : ι → Type*} [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSpace (β i)]  (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (ν : (i : ι) → Measure (β i)) [∀ i, SigmaFinite (ν i)] {f : (i : ι) → (α i) → (β i)}
    (hf : ∀ i, MeasurePreserving (f i) (μ i) (ν i)) :
    MeasurePreserving (fun a i ↦ f i (a i)) (Measure.pi μ) (Measure.pi ν) where
  measurable :=
    measurable_pi_iff.mpr <| fun i ↦ (hf i).measurable.comp (measurable_pi_apply i)
  map_eq := by
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    rw [Measure.map_apply, Set.preimage_pi, Measure.pi_pi]
    simp_rw [← MeasurePreserving.measure_preimage (hf _) (hs _)]
    · exact measurable_pi_iff.mpr <| fun i ↦ (hf i).measurable.comp (measurable_pi_apply i)
    · exact MeasurableSet.univ_pi hs

theorem volume_preserving_pi {ι : Type*} [Fintype ι] {α' β' : ι → Type*} [∀ i, MeasureSpace (α' i)]
    [∀ i, MeasureSpace (β' i)] [∀ i, SigmaFinite (volume : Measure (α' i))]
    [∀ i, SigmaFinite (volume : Measure (β' i))] {f : (i : ι) → (α' i) → (β' i)}
    (hf : ∀ i, MeasurePreserving (f i)) :
    MeasurePreserving (fun (a : (i : ι) → α' i) (i : ι) ↦ (f i) (a i)) :=
  measurePreserving_pi _ _ hf

theorem Real.rpow_ne_zero_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y ≠ 0 := by
  rw [rpow_def_of_pos hx]; apply exp_ne_zero _

theorem Basis.total_eq_iff_eq_repr {M R ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (B : Basis ι R M) (x : M) (c : ι →₀ R) : Finsupp.total ι M R B c = x ↔ c = B.repr x :=
  ⟨fun h ↦ by rw [← h, B.repr_total], fun h ↦ by rw [h, B.total_repr]⟩

-- Is it a good idea to use equivFun?
theorem Basis.sum_eq_iff_eq_equivFun {M R ι : Type*} [Fintype ι] [Semiring R] [AddCommMonoid M]
    [Module R M] (B : Basis ι R M) (x : M) (c : ι → R) :
    ∑ i, (c i) • (B i) = x ↔ c = B.equivFun x :=
  ⟨fun h ↦ by rw [← h, B.equivFun_apply, B.repr_sum_self], fun h ↦ by rw [h, B.sum_equivFun]⟩

theorem ContinuousLinearEquiv.image_interior {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type*} [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂)  (s : Set M₁) :
    e '' interior s = interior (e '' s) :=
  e.toHomeomorph.image_interior s

theorem ContinuousLinearEquiv.preimage_interior {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type*} [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e ⁻¹' interior s = interior (e ⁻¹' s) :=
  e.toHomeomorph.preimage_interior s

-- open Classical in
-- theorem MeasureTheory.measurePreserving_subtypeEquivRight
--     {α : Type*} [MeasurableSpace α] {p : α → Prop} {q : α → Prop} (hq : MeasurableSet {x | q x})
--     (e : ∀ (x : α), p x ↔ q x) (μ : Measure α) :
--     MeasurePreserving (Equiv.subtypeEquivRight e) (comap Subtype.val μ) (comap Subtype.val μ) := by
--   have h : Measurable (Equiv.subtypeEquivRight e) := by
--     rw [Equiv.subtypeEquivRight]
--     exact Measurable.subtype_map (fun ⦃t⦄ a ↦ a) fun x ↦ (e x).mp
--   have hp : MeasurableSet {x | p x} := by
--     simp_rw [measurableSet_setOf]
--     exact measurableSet_setOf.mp hq
--   refine ⟨h, ?_⟩
--   ext s hs
--   have : Subtype.val '' ((Equiv.subtypeEquivRight e) ⁻¹' s) = Subtype.val '' s := by
--     ext; aesop
--   rw [map_apply h hs, comap_apply _ Subtype.val_injective _ _ hs, comap_apply _
--     Subtype.val_injective _ _ (h hs), this]
--   exact fun _ ↦  MeasurableSet.subtype_image hp
--   exact fun _ ↦  MeasurableSet.subtype_image hq

def ContinuousLinearEquiv.piCongrRight {R : Type*} [Semiring R] {ι : Type*} {M : ι → Type*}
    [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {N : ι → Type*}
    [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : (i : ι) → M i ≃L[R] N i) :
    ((i : ι) → M i) ≃L[R] (i : ι) → N i :=
  { LinearEquiv.piCongrRight fun i ↦ f i with
    continuous_toFun := by
      exact continuous_pi fun i ↦ (f i).continuous_toFun.comp (continuous_apply i)
    continuous_invFun := by
      exact continuous_pi fun i => (f i).continuous_invFun.comp (continuous_apply i) }

@[simp]
theorem ContinuousLinearEquiv.piCongrRight_apply {R : Type*} [Semiring R] {ι : Type*}
    {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : (i : ι) → M i ≃L[R] N i) (m : (i : ι) → M i) (i : ι) :
    ContinuousLinearEquiv.piCongrRight f m i = (f i) (m i) := rfl

@[simp]
theorem ContinuousLinearEquiv.piCongrRight_symm_apply {R : Type*} [Semiring R] {ι : Type*}
    {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : (i : ι) → M i ≃L[R] N i) (n : (i : ι) → N i) (i : ι) :
    (ContinuousLinearEquiv.piCongrRight f).symm n i = (f i).symm (n i) := rfl

def ContinuousLinearEquiv.neg (R : Type*) {M : Type*} [Semiring R] [AddCommGroup M]
    [TopologicalSpace M] [ContinuousNeg M] [Module R M] :
    M ≃L[R] M :=
  { LinearEquiv.neg R with
    continuous_toFun := continuous_neg
    continuous_invFun := continuous_neg }

@[simp]
theorem ContinuousLinearEquiv.coe_neg {R : Type*} {M : Type*} [Semiring R] [AddCommGroup M]
    [TopologicalSpace M] [ContinuousNeg M] [Module R M] :
    ⇑(neg R : M ≃L[R] M) = -id := rfl

@[simp]
theorem ContinuousLinearEquiv.neg_apply {R : Type*} {M : Type*} [Semiring R] [AddCommGroup M]
    [TopologicalSpace M] [ContinuousNeg M] [Module R M] (x : M) : neg R x = -x := by simp

@[simp]
theorem ContinuousLinearEquiv.symm_neg {R : Type*} {M : Type*} [Semiring R] [AddCommGroup M]
    [TopologicalSpace M] [ContinuousNeg M] [Module R M] :
    (neg R : M ≃L[R] M).symm = neg R := rfl

open MeasureTheory

section marginal

variable {δ : Type*} {π : δ → Type*} [DecidableEq δ] [(x : δ) → MeasurableSpace (π x)]
    (μ : (i : δ) → MeasureTheory.Measure (π i)) {s : Finset δ}

theorem Measurable.lmarginal_zero {x : (i : δ) → π i} :
    (∫⋯∫⁻_s, 0 ∂μ) x = 0 := lintegral_zero

theorem Measurable.lmarginal_update [∀ (i : δ), SigmaFinite (μ i)]
    {f : ((i : δ) → π i) → ENNReal} (hf : Measurable f) {x : (i : δ) → π i} (i : δ) :
    Measurable fun xᵢ ↦ (∫⋯∫⁻_s, f ∂μ) (Function.update x i xᵢ) := by
  exact (Measurable.lmarginal _ hf).comp (measurable_update x)

theorem MeasureTheory.lmarginal_const_smul
    {f : ((i : δ) → π i) → ENNReal} (hf : Measurable f) {x : (i : δ) → π i} (r : ENNReal) :
    (∫⋯∫⁻_s, r • f ∂μ) x = r * (∫⋯∫⁻_s, f ∂μ) x := by
  simp_rw [lmarginal, Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul _ (by convert hf.comp measurable_updateFinset)]

theorem MeasureTheory.lmarginal_const_smul'
    {f : ((i : δ) → π i) → ENNReal} {x : (i : δ) → π i} (r : ENNReal) (hr : r ≠ ⊤):
    (∫⋯∫⁻_s, r • f ∂μ) x = r * (∫⋯∫⁻_s, f ∂μ) x := by
  simp_rw [lmarginal, Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hr]

end marginal

open NNReal ENNReal Real

theorem one_step₀ (f : ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ z : ℂ, f ‖z‖ = 2 * NNReal.pi * ∫⁻ x in Set.Ioi 0, x.toNNReal * (f x) := by
  calc ∫⁻ (z : ℂ), f ‖z‖
    = ∫⁻ p in polarCoord.target, p.1.toNNReal * f |p.1| := by
        rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp,
          ← lintegral_comp_polarCoord_symm]
        · simp_rw [polarCoord_symm_apply, Complex.measurableEquivRealProd_symm_apply,
            Complex.norm_eq_abs, Complex.abs_eq_sqrt_sq_add_sq, mul_pow, ← mul_add,
            cos_sq_add_sin_sq, mul_one, sqrt_sq_eq_abs, ENNReal.smul_def, smul_eq_mul]
        · exact hf.comp measurable_norm
    _ = ∫⁻ _x in Set.Ioo (-π) π, ∫⁻ y in Set.Ioi (0 : ℝ), y.toNNReal * f |y| := by
        rw [lintegral_lintegral_symm, polarCoord_target, Measure.prod_restrict, volume_eq_prod]
        exact Measurable.aemeasurable <|
          measurable_snd.ennreal_ofReal.mul <| hf.comp measurable_snd.norm
    _ = 2 * NNReal.pi * ∫⁻ x in Set.Ioi 0, x.toNNReal * (f x) := by
        rw [lintegral_const, restrict_apply MeasurableSet.univ, Set.univ_inter, volume_Ioo,
          sub_neg_eq_add, ← two_mul, mul_comm, ofReal_mul zero_le_two, ofReal_ofNat,
          ← coe_real_pi, ofReal_coe_nnreal]
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioi ?_
        filter_upwards with _ hx using by rw [abs_of_pos (by convert hx)]

theorem multiple_step₀ {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ENNReal)
    (hf : Measurable f) (s : Finset ι) (a : ι → ℂ) :
    (∫⋯∫⁻_s, fun z ↦ (f fun i ↦ ‖z i‖) ∂fun _ ↦ (volume : Measure ℂ)) a =
      (2 * NNReal.pi) ^ s.card *
        (∫⋯∫⁻_s, fun x ↦ (∏ i ∈ s, (x i).toNNReal) * f x
          ∂fun _ ↦ (volume.restrict (Set.Ioi (0 : ℝ)))) fun i ↦ ‖a i‖ := by
   induction s using Finset.induction generalizing a with
  | empty => simp
  | @insert i s hi h_ind =>
      have h₀ : ∀ (xᵢ : ℂ) (i j : ι),
          ‖Function.update a j xᵢ i‖ = Function.update (fun j ↦ ‖a j‖) j ‖xᵢ‖ i :=
        fun _ _ _ ↦ by rw [Function.update_apply, Function.update_apply, apply_ite norm]
      rw [lmarginal_insert _ ?_ hi]
      swap;
      · refine hf.comp (measurable_pi_lambda _ fun _ ↦ (measurable_pi_apply _).norm)
      simp_rw [h_ind, h₀]
      have h₁ : ∀ t : Finset ι, Measurable fun x ↦ (∏ i ∈ t, (x i).toNNReal) * f x := by
        refine fun t ↦ ((Finset.measurable_prod t ?_).coe_nnreal_ennreal).mul hf
        exact fun _ _ ↦ (measurable_pi_apply _).real_toNNReal
      have := one_step₀ (fun z ↦ (∫⋯∫⁻_s, fun x ↦ (∏ i ∈ s, (x i).toNNReal) * f x
            ∂fun _ ↦ (volume.restrict (Set.Ioi (0 : ℝ))))
            fun k ↦ Function.update (fun j ↦ ‖a j‖) i z k) ?_
      swap
      · refine ((h₁ s).lmarginal _).comp (measurable_pi_lambda _ fun _ ↦ Measurable.eval ?_)
        exact (measurable_update _).comp' measurable_id'
      rw [lintegral_const_mul _ ?_]
      swap;
      · exact ((h₁ s).lmarginal _).comp
          <| measurable_pi_lambda _ fun _ ↦ ((measurable_update _).comp' measurable_norm).eval
      rw [this]; clear this
      rw [lmarginal_insert _ ?_ hi]
      swap;
      · exact h₁ (insert i s)
      simp_rw [← lmarginal_const_smul' _  _ coe_ne_top]
      rw [Finset.card_insert_of_not_mem hi]
      rw [← mul_assoc, ← pow_succ]
      simp_rw [Finset.prod_insert hi]
      have : ∀ y : ℝ, Measurable
          ((y.toNNReal : ENNReal) • fun x ↦ ↑(∏ i ∈ s, (x i).toNNReal) * f x) := by
        intro y
        exact Measurable.const_smul (h₁ s) _
      simp_rw [lmarginal_update_of_not_mem (this _) hi]
      have : Measurable fun x ↦ ↑((x i).toNNReal * ∏ i ∈ s, (x i).toNNReal) * f x := by
        simp_rw [coe_mul, mul_assoc]
        refine Measurable.mul ?_ ?_
        · refine Measurable.ennreal_ofReal ?_
          exact measurable_pi_apply i
        · exact h₁ s
      simp_rw [lmarginal_update_of_not_mem this hi]
      simp only [coe_finset_prod, Function.comp, Pi.smul_apply, smul_eq_mul,
        coe_mul, Function.update_same, mul_assoc]

theorem one_step (f : ℝ → ENNReal) (hf₀ : Measurable f) (hf₁ : ∀ ⦃x⦄, x ≤ 0 → f x = 0) :
    ∫⁻ z : ℂ, f ‖z‖ = 2 * NNReal.pi * ∫⁻ x, ‖x‖₊ * (f x) := by
  sorry
  -- calc ∫⁻ (z : ℂ), f ‖z‖
  --   = ∫⁻ p in polarCoord.target, |p.1|.toNNReal * f |p.1| := by
  --       rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp,
  --         ← lintegral_comp_polarCoord_symm]
  --       · simp_rw [polarCoord_symm_apply, Complex.measurableEquivRealProd_symm_apply,
  --           Complex.norm_eq_abs, Complex.abs_eq_sqrt_sq_add_sq, mul_pow, ← mul_add,
  --           cos_sq_add_sin_sq, mul_one, sqrt_sq_eq_abs, ENNReal.smul_def, smul_eq_mul]
  --       · exact hf₀.comp measurable_norm
  --   _ = ∫⁻ _x in Set.Ioo (-π) π, ∫⁻ y in Set.Ioi (0 : ℝ), |y|.toNNReal * f |y| := by
  --       rw [lintegral_lintegral_symm, polarCoord_target, Measure.prod_restrict, volume_eq_prod]
  --       exact Measurable.aemeasurable <|
  --         (measurable_id.ennreal_ofReal.mul hf₀).comp (measurable_norm.comp measurable_snd)
  --   _ = 2 * NNReal.pi * ∫⁻ x, (Set.Ioi 0).indicator (fun y ↦ |y|.toNNReal * f |y|) x := by
  --       rw [lintegral_const, restrict_apply MeasurableSet.univ, Set.univ_inter, volume_Ioo,
  --         sub_neg_eq_add, ← two_mul, mul_comm, ofReal_mul zero_le_two, ofReal_ofNat,
  --         ← coe_real_pi, ofReal_coe_nnreal, ← lintegral_indicator _ measurableSet_Ioi]
  --   _ = 2 * NNReal.pi * ∫⁻ (x : ℝ), ‖x‖₊ * f x := by
  --       congr 2; ext x
  --       rw [Set.indicator_apply]
  --       split_ifs with h
  --       · rw [ennnorm_eq_ofReal_abs, abs_eq_self.mpr (Set.mem_Ioi.mp h).le]
  --         rfl
  --       · rw [hf₁ (Set.not_mem_Ioi.mp h), mul_zero]

theorem multiple_step {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ENNReal)
    (hf₀ : Measurable f) (hf₁ : ∀ ⦃x xᵢ i⦄, xᵢ ≤ 0 → f (Function.update x i xᵢ) = 0)
    (s : Finset ι) (a : ι → ℂ) :
    (∫⋯∫⁻_s, fun z ↦ (f fun i ↦ ‖z i‖) ∂fun _ ↦ (volume : Measure ℂ)) a =
      (2 * NNReal.pi) ^ s.card *
        (∫⋯∫⁻_s, (fun x ↦ (∏ i ∈ s, ‖x i‖₊) * f x) ∂fun _ ↦ (volume : Measure ℝ))
          (fun i ↦ ‖a i‖) := by
  induction s using Finset.induction generalizing a with
  | empty => simp
  | @insert i s hi h_ind =>
    have h₀ : ∀ (xᵢ : ℂ) (i j : ι),
        ‖Function.update a j xᵢ i‖ = Function.update (fun j ↦ ‖a j‖) j ‖xᵢ‖ i := by
      intro _ _ _
      rw [Function.update_apply, Function.update_apply, apply_ite norm]
    have h₁ : Measurable fun z : ι → ℂ ↦ f fun i ↦ ‖z i‖ :=
      hf₀.comp (measurable_pi_iff.mpr fun _ ↦ measurable_norm.comp (measurable_pi_apply _))
    have h₄ : ∀ t : Finset ι, Measurable fun x ↦ (∏ i ∈ t, ‖x i‖₊) * f x := by
      intro t
      simp_rw [coe_finset_prod]
      refine Measurable.mul ?_ hf₀
      refine Finset.measurable_prod _ fun _ _ ↦ ?_
      simp only [measurable_coe_nnreal_ennreal_iff]
      exact measurable_nnnorm.comp (measurable_pi_apply _)
    have h₃ : Measurable fun xᵢ ↦
        (∫⋯∫⁻_s, fun x ↦ ↑(∏ i ∈ s, ‖x i‖₊) * f x ∂fun x ↦ volume)
          fun j ↦ Function.update (fun j ↦ ‖a j‖) i xᵢ j := by
      refine Measurable.lmarginal_update (fun _ : ι ↦ (volume : Measure ℝ)) ?_ _
      exact h₄ s
    have h₂ : Measurable fun xᵢ : ℂ ↦
        (∫⋯∫⁻_s, fun x ↦ (∏ i ∈ s, ‖x i‖₊) * f x ∂fun x ↦ volume)
          fun k ↦ Function.update (fun j ↦ ‖a j‖) i ‖xᵢ‖ k := by
      have t1 : Measurable fun xᵢ : ℂ ↦ ‖xᵢ‖ := by exact measurable_norm
      have := Measurable.comp h₃ t1
      exact this
    have h₅ : ∀ ⦃x : ℝ⦄, x ≤ 0 →
        ((∫⋯∫⁻_s, fun x ↦ ↑(∏ i ∈ s, ‖x i‖₊) * f x ∂fun x ↦ volume)
          fun j ↦ Function.update (fun j ↦ ‖a j‖) i x j) = 0 := by
      intro y hy
      rw [lmarginal_update_of_not_mem (h₄ s) hi (fun j ↦ ‖a j‖) y]
      simp_rw [(·∘·)]
      convert Measurable.lmarginal_zero _
      rw [hf₁ hy, mul_zero, Pi.zero_apply]
      infer_instance
    have h₆ : Measurable fun x ↦ (∏ i ∈ s, ‖x i‖₊) * f x := by
      exact h₄ s
    have h₇ : ∀ xᵢ : ℝ, Measurable fun x ↦ ‖xᵢ‖₊ • (↑(∏ j ∈ s, ‖x j‖₊) * f x) := by
      intro _
      refine Measurable.const_smul ?_ _
      exact h₄ s
    have h₈ : Measurable fun x ↦ (‖x i‖₊ * ∏ i ∈ s, ‖x i‖₊) * f x := by
      simp_rw [mul_assoc]
      refine Measurable.mul ?_ ?_
      · simp only [measurable_coe_nnreal_ennreal_iff]
        exact measurable_nnnorm.comp (measurable_pi_apply _)
      · exact h₄ s
    calc
    _ = ((2 * pi) ^ s.card * ∫⁻ (xᵢ : ℂ),
          (∫⋯∫⁻_s, fun x ↦ (∏ i ∈ s, ‖x i‖₊) * f x ∂fun x ↦ volume) fun k ↦
            Function.update (fun j ↦ ‖a j‖) i ‖xᵢ‖ k) := by
        rw [lmarginal_insert _ h₁ hi, ← lintegral_const_mul _ h₂]
        simp_rw [h_ind, h₀]
    _ = ((2 * pi) ^ (s.card + 1) * ∫⁻ (xᵢ : ℝ), ‖xᵢ‖₊ *
          (∫⋯∫⁻_s, fun x ↦ (∏ i ∈ s, ‖x i‖₊) * f x ∂fun x ↦ volume)
            fun j ↦ Function.update (fun j ↦ ‖a j‖) i xᵢ j) := by
        rw [pow_succ, mul_assoc, ← one_step _ h₃ h₅]
    _ = (2 * pi) ^ (insert i s).card *
          (∫⋯∫⁻_insert i s, fun x ↦ (∏ i ∈ insert i s, ‖x i‖₊) * f x ∂fun x ↦ volume)
            fun j ↦ ‖a j‖ := by
        conv_lhs =>
          enter [2, 2, xᵢ]
          rw [← lmarginal_const_smul _ h₆, Pi.smul_def]
          rw [lmarginal_update_of_not_mem (by convert h₇ xᵢ) hi]
        rw [lmarginal_insert, Finset.card_insert_of_not_mem hi]
        simp_rw [smul_eq_mul, Finset.prod_insert hi]
        conv_rhs =>
          enter [2,2, xᵢ]
          rw [lmarginal_update_of_not_mem (by convert h₈) hi]
        simp only [(·∘·)]
        congr
        ext x
        congr
        ext
        simp
        rw [mul_assoc]
        exact h₄ _
        exact hi

section Topo

open Set

theorem closure_lt_eq_le {α β : Type*} [TopologicalSpace α] [PartialOrder α] [OrderClosedTopology α]
    [TopologicalSpace β] {f : β → α}  {g : β → α} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ ⦃x⦄, f x = g x → ∃ᶠ y in nhds x, f y < g y) :
    closure {b | f b < g b} = {b | f b ≤ g b} := by
  refine le_antisymm (closure_lt_subset_le hf hg) fun x hx ↦ ?_
  obtain (hx₁| hx₂) := le_iff_eq_or_lt.mp hx
  · exact mem_closure_iff_frequently.mpr (h hx₁)
  · exact subset_closure hx₂

theorem frontier_le_eq_eq {α β : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {f : β → α} {g : β → α} [TopologicalSpace β] (hf : Continuous f)  (hg : Continuous g)
    (h : ∀ ⦃x⦄, g x = f x → ∃ᶠ y in nhds x, g y < f y) :
    frontier {b | f b ≤ g b} = {b | f b = g b} := by
  rw [frontier_eq_closure_inter_closure, closure_le_eq hf hg]
  ext x
  rw [show {x | f x ≤ g x}ᶜ = {x | g x < f x} by ext; simp, closure_lt_eq_le hg hf h]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, le_antisymm_iff]

theorem frontier_lt_eq_eq {α β : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {f : β → α} {g : β → α} [TopologicalSpace β] (hf : Continuous f)  (hg : Continuous g)
    (h : ∀ ⦃x⦄, f x = g x → ∃ᶠ y in nhds x, f y < g y) :
    frontier {b | f b < g b} = {b | f b = g b} := by
  simpa only [eq_comm, ← not_lt, ← Set.compl_setOf, frontier_compl] using frontier_le_eq_eq hg hf h

end Topo

#exit

-- section Module

-- variable {ι : Type*} [IsEmpty ι] (M : Type*) [AddCommMonoid M] {R : Type*} [Semiring R] [Module R M]
-- variable (b : Basis ι R M)

-- example : Subsingleton M := by
--   have : Fintype ι := Fintype.ofIsEmpty
--   exact subsingleton_of_forall_eq 0 fun y ↦ by rw [← b.sum_repr y, Fintype.sum_empty]

-- end Module

section PiLp

open Bornology Filter BigOperators

variable {ι : Type*} [Fintype ι] {R M : Type*} [NormedDivisionRing R] [SeminormedAddCommGroup M]
  [Module R M] [BoundedSMul R M]

theorem Bornology.isBoundedOfBoundedCoeff (v : ι → M) {s : Set R} (h : IsBounded s) :
    IsBounded (Set.range fun (c : ι → s) ↦ ∑ i, (c i : R) • v i) := by
  generalize Finset.univ (α := ι) = t
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ s, ‖x‖ ≤ C := isBounded_iff_forall_norm_le.mp h
  induction t using Finset.cons_induction_on with
  | h₁ =>
      exact Metric.isBounded_range_iff.mpr ⟨0, by simp⟩
  | @h₂ a _ h_ne h_bd =>
      rw [isBounded_iff_forall_norm_le] at h_bd ⊢
      obtain ⟨C₁, hC₁⟩ := h_bd
      refine ⟨C * ‖v a‖ + C₁, fun x ⟨c, hc⟩ ↦ ?_⟩
      simp_rw [← hc, Finset.sum_cons]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_smul]
      gcongr
      · exact hC (c a) (c a).prop
      · exact hC₁ _ ⟨c, rfl⟩

end PiLp

section FundamentalCone

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
  BigOperators Submodule Bornology NumberField.Units NumberField.Units.dirichletUnitTheorem

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

variable (K : Type*) [Field K] [NumberField K]

/-- Docs. -/
abbrev S : Set (E K) := {x ∈ fundamentalCone K | mixedEmbedding.norm x ≤ 1}

/-- Docs. -/
abbrev S₁ : Set (E K) := {x ∈ fundamentalCone K | mixedEmbedding.norm x = 1}

variable {K} in
@[simp]
theorem logMap_eq_of_norm_one_at_isReal {x : E K} (hx : mixedEmbedding.norm x = 1)
    {w : InfinitePlace K} (hw : IsReal w) (hw' : w ≠ w₀) :
    logMap x ⟨w, hw'⟩ = Real.log ‖x.1 ⟨w, hw⟩‖ := by
  rw [logMap, dif_pos hw, hx, Real.log_one, zero_mul, sub_zero]

variable {K} in
@[simp]
theorem logMap_eq_of_norm_one_at_isComplex {x : E K} (hx : mixedEmbedding.norm x = 1)
    {w : InfinitePlace K} (hw : IsComplex w) (hw' : w ≠ w₀) :
    logMap x ⟨w, hw'⟩ = 2 * Real.log ‖x.2 ⟨w, hw⟩‖ := by
  rw [logMap, dif_neg (not_isReal_iff_isComplex.mpr hw), hx, Real.log_one, zero_mul, sub_zero]

variable {K} in
open Classical in
noncomputable def atPlace (w : InfinitePlace K) : (E K) →*₀ ℝ where
  toFun x := if hw : IsReal w then ‖x.1 ⟨w, hw⟩‖ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by split_ifs <;> simp

theorem atPlace_apply_isReal (x : E K) {w : InfinitePlace K} (hw : IsReal w) :
    atPlace w x = ‖x.1 ⟨w, hw⟩‖ := by
  rw [atPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_pos]

theorem atPlace_apply_isComplex (x : E K) {w : InfinitePlace K} (hw : IsComplex w) :
    atPlace w x = ‖x.2 ⟨w, hw⟩‖ := by
  rw [atPlace, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_neg (not_isReal_iff_isComplex.mpr hw)]



set_option maxHeartbeats 5000000 in
theorem norm_apply' (x : E K) :
    mixedEmbedding.norm x = ∏ w, (atPlace x w) ^ (mult w) := by
  classical
  simp_rw [mixedEmbedding.norm_apply, atPlace, dite_pow, Finset.univ.prod_dite]
  simp_rw [← Finset.prod_coe_sort_eq_attach]
  rw [← Finset.prod_coe_sort, ← Finset.prod_coe_sort]

  ·

    sorry
  ·
    sorry

#exit

example :
  ∃ C, 0 < C ∧ ∀ x (hx : mixedEmbedding.norm x = 1) w, w ≠ w₀ →


theorem isBounded_S : IsBounded (S₁ K) := by
  classical
  rsuffices ⟨C, hC⟩ :
      ∃ C, ∀ x ∈ S₁ K, ∀ w, w ≠ w₀ → if hw : IsReal w then |Real.log ‖x.1 ⟨w, hw⟩‖| ≤ C else
      |Real.log ‖(x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩)‖| ≤ C := by
    sorry
  refine isBounded_image_fst_and_snd.mp ⟨?_, ?_⟩
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨max (Real.exp C) 2, ?_⟩
    rintro x₁ ⟨x, hx, rfl⟩
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists, exists_and_right,
      exists_eq_right] at hx
    rw [pi_norm_le_iff_of_nonneg]
    rintro ⟨w, hw⟩
    by_cases hw' : w = w₀
    · have := hx.2
      rw [mixedEmbedding.norm_apply] at this
      rw [hw'] at hw
      rw [← Finset.univ.mul_prod_erase _ (by sorry : ⟨w₀, hw⟩  ∈ Finset.univ)]
        at this
      sorry
    · specialize hC x hx w hw'
      rw [dif_pos] at hC

      sorry
  ·
    sorry

#exit

  classical
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  obtain ⟨r, hr₁, hr₂⟩ := (Zspan.fundamentalDomain_isBounded B).subset_closedBall_lt 0 0
  have h₀ : ∀ x ∈ fundamentalCone K,
    ‖logMap x‖ ≤ r := fun _ h ↦ mem_closedBall_zero_iff.mp (hr₂ h.1)
  have : ∀ x ∈ S₁ K, ∀ w, w ≠ w₀ →
      if hw : IsReal w then |Real.log ‖x.1 ⟨w, hw⟩‖| ≤ r
      else |Real.log ‖(x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩)‖| ≤ r / 2 := by
    intro x hx w hw'
    split_ifs with hw
    · rw [← logMap_eq_of_norm_one_at_isReal hx.2 hw hw']
      exact (pi_norm_le_iff_of_nonneg hr₁.le).mp (h₀ x hx.1) ⟨w, hw'⟩
    · rw [le_div_iff' zero_lt_two, show (2 : ℝ) = |2| by norm_num, ← abs_mul,
        ← logMap_eq_of_norm_one_at_isComplex hx.2 (not_isReal_iff_isComplex.mp hw) hw']
      exact (pi_norm_le_iff_of_nonneg hr₁.le).mp (h₀ x hx.1) ⟨w, hw'⟩
  have : ∀ x ∈ S₁ K, if hw₀ : IsReal w₀ then |Real.log ‖x.1 ⟨w₀, hw₀⟩‖| ≤ r
      else |Real.log ‖(x.2 ⟨w₀, not_isReal_iff_isComplex.mp hw₀⟩)‖| ≤ r / 2 := sorry

  rw [isBounded_iff_forall_norm_le]
  refine ⟨?_, fun x hx ↦ ?_⟩
  rotate_left
  refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg sorry]
    intro w

#exit

theorem measurable_S : MeasurableSet (S K) :=
  fundamentalCone.measurable.inter <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

theorem frontier_S_eq : frontier (S K) = S₁ K := sorry

open Classical in
theorem frontier_ae_null : volume (S₁ K) = 0 := sorry

end FundamentalCone

noncomputable section

open Classical

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField.mixedEmbedding.euclideanSpace

open NumberField NumberField.InfinitePlace MeasureTheory BigOperators Submodule

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E₂" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

/-- Docs. -/
local instance : Ring (EuclideanSpace ℝ { w : InfinitePlace K // IsReal w }) := Pi.ring

/-- Docs. -/
local instance : Ring (EuclideanSpace ℂ { w : InfinitePlace K // IsComplex w }) := Pi.ring

instance : Ring (E₂ K) := Prod.instRing

instance : MeasurableSpace (E₂ K) := borel _

instance : BorelSpace (E₂ K)  :=  ⟨rfl⟩

instance : T2Space (E₂ K) := Prod.t2Space

protected theorem norm_apply (x : E₂ K) :
    ‖x‖ = Real.sqrt (∑ w, ‖x.1 w‖ ^ 2 + ∑ w, ‖x.2 w‖ ^ 2) := by
  rw [WithLp.prod_norm_eq_add (by exact Nat.ofNat_pos), EuclideanSpace.norm_eq,
    EuclideanSpace.norm_eq, ENNReal.toReal_ofNat, Real.rpow_two, Real.sq_sqrt (by positivity),
    Real.rpow_two, Real.sq_sqrt (by positivity), Real.sqrt_eq_rpow]

-- protected theorem inner_apply (x y : E₂ K) :
--     ⟪x, y⟫_ℝ = ∑ w, (x.1 w) * (y.1 w) +
--       ∑ w, ((x.2 w).re * (y.2 w).re + (x.2 w).im * (y.2 w).im) := by
--   simp_rw [WithLp.prod_inner_apply, EuclideanSpace.inner_eq_star_dotProduct, real_inner_eq_re_inner,
--     EuclideanSpace.inner_eq_star_dotProduct, Matrix.dotProduct, Pi.star_apply, star_trivial,
--     RCLike.star_def, map_sum, RCLike.mul_re, RCLike.conj_re, RCLike.re_to_complex,
--     RCLike.conj_im, WithLp.equiv_pi_apply, neg_mul, sub_neg_eq_add, RCLike.im_to_complex]

/-- Docs. -/
protected def linearEquiv : (E₂ K) ≃ₗ[ℝ] (E K) := WithLp.linearEquiv _ _ _

/-- Docs. -/
protected def continuousLinearEquiv : (E₂ K) ≃L[ℝ] (E K) :=
  (euclideanSpace.linearEquiv K).toContinuousLinearEquiv

/-- Docs. -/
protected def homeomorph : (E₂ K) ≃ₜ (E K) :=
  (euclideanSpace.continuousLinearEquiv K).toHomeomorph

/-- Docs. -/
-- protected def addEquiv : (E₂ K) ≃+ (E K) := (euclideanSpace.linearEquiv K).toAddEquiv

protected theorem coe_homeomorph :
   ⇑(euclideanSpace.linearEquiv K) = ⇑(euclideanSpace.homeomorph K) := rfl

protected theorem coe_continuousLinearEquiv :
    ⇑(euclideanSpace.linearEquiv K) = ⇑(euclideanSpace.continuousLinearEquiv K) := rfl

@[simp]
theorem linearEquiv_apply_ofIsReal (x : E₂ K) {w : InfinitePlace K} (hw : IsReal w) :
    (euclideanSpace.linearEquiv K x).1 ⟨w, hw⟩ = x.1 ⟨w, hw⟩ := rfl

@[simp]
theorem linearEquiv_apply_ofIsComplex (x : E₂ K) {w : InfinitePlace K} (hw : IsComplex w) :
    (euclideanSpace.linearEquiv K x).2 ⟨w, hw⟩ = x.2 ⟨w, hw⟩ := rfl

instance : Nontrivial (E₂ K) := (euclideanSpace.linearEquiv K).toEquiv.nontrivial

protected theorem finrank :
    FiniteDimensional.finrank ℝ (E₂ K) = FiniteDimensional.finrank ℚ K := by
  rw [← mixedEmbedding.finrank]
  refine  LinearEquiv.finrank_eq ?_
  exact euclideanSpace.linearEquiv K

/-- Docs. -/
protected def stdOrthonormalBasis : OrthonormalBasis (index K) ℝ (E₂ K) :=
  OrthonormalBasis.prod (EuclideanSpace.basisFun _ ℝ)
    ((Pi.orthonormalBasis fun _ ↦ Complex.orthonormalBasisOneI).reindex (Equiv.sigmaEquivProd _ _))

theorem stdOrthonormalBasis_map_equiv :
    (euclideanSpace.stdOrthonormalBasis K).toBasis.map (euclideanSpace.linearEquiv K) =
      mixedEmbedding.stdBasis K := by ext _ _ <;> rfl

@[simp]
theorem stdOrthonormalBasis_repr_apply (x : E₂ K) (i : index K) :
    (euclideanSpace.stdOrthonormalBasis K).repr x i =
      (stdBasis K).repr (euclideanSpace.linearEquiv K x) i := rfl

theorem measurePreserving_euclideanLinearEquiv :
    MeasurePreserving (euclideanSpace.linearEquiv K) := by
  let e := (euclideanSpace.homeomorph K).toMeasurableEquiv
  convert e.measurable.measurePreserving volume
  erw [← (OrthonormalBasis.addHaar_eq_volume (euclideanSpace.stdOrthonormalBasis K)),
    Homeomorph.toMeasurableEquiv_coe, Basis.map_addHaar _ (euclideanSpace.continuousLinearEquiv K),
    stdOrthonormalBasis_map_equiv, eq_comm, Basis.addHaar_eq_iff, Basis.coe_parallelepiped,
    ← measure_congr (Zspan.fundamentalDomain_ae_parallelepiped (stdBasis K) volume),
    volume_fundamentalDomain_stdBasis K]

end NumberField.mixedEmbedding.euclideanSpace

open Filter NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Topology MeasureTheory
  NumberField.Units NumberField.mixedEmbedding.fundamentalCone Submodule Bornology
  NumberField.mixedEmbedding.euclideanSpace FiniteDimensional NumberField.Units.dirichletUnitTheorem

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K` as an Euclidean space. -/
local notation "E₂" K =>
    (WithLp 2 ((EuclideanSpace ℝ {w : InfinitePlace K // IsReal w}) ×
      (EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})))

local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- Docs. -/
def Λ : AddSubgroup (E₂ K) :=
    (span ℤ (Set.range ((latticeBasis K).map (euclideanSpace.linearEquiv K).symm))).toAddSubgroup

instance : DiscreteTopology (Λ K) := Zspan.instDiscreteTopology _

instance : IsZlattice ℝ (Λ K) where
  span_top := by
    simp_rw [Λ, coe_toAddSubgroup, ← Zspan.map, map_coe, LinearEquiv.restrictScalars_apply,
      ← Submodule.map_span, Zspan.span_top, Submodule.map_top, LinearEquivClass.range]

abbrev X : Set (E₂ K) := (euclideanSpace.linearEquiv K)⁻¹' (fundamentalCone K)

theorem repl :
  {x | x ∈ X K ∧ mixedEmbedding.norm ((euclideanSpace.linearEquiv K) x) ≤ 1} =
    (euclideanSpace.linearEquiv K)⁻¹' (S K) := rfl

theorem repl' :
  {x | x ∈ X K ∧ mixedEmbedding.norm ((euclideanSpace.linearEquiv K) x) = 1} =
    (euclideanSpace.linearEquiv K)⁻¹' (S₁ K) := rfl

example :
    IsBounded {x | x ∈ X K ∧ mixedEmbedding.norm ((euclideanSpace.linearEquiv K) x) ≤ 1} := by
  have := (euclideanSpace.continuousLinearEquiv K).symm.lipschitz
  have : AntilipschitzWith _ (euclideanSpace.linearEquiv K) := by
    refine this.to_rightInverse ?_
    exact Equiv.rightInverse_symm _
  exact AntilipschitzWith.isBounded_preimage this (isBounded_S K)

example :
    MeasurableSet {x | x ∈ X K ∧ mixedEmbedding.norm ((euclideanSpace.linearEquiv K) x) ≤ 1} := by
  have : Measurable (euclideanSpace.linearEquiv K) :=
    (euclideanSpace.continuousLinearEquiv K).continuous.measurable
  exact MeasurableSet.preimage (measurable_S K) this

example :
    frontier {x | x ∈ X K ∧ mixedEmbedding.norm ((euclideanSpace.linearEquiv K) x) ≤ 1} =
      {x | x ∈ X K ∧ mixedEmbedding.norm ((euclideanSpace.linearEquiv K) x) = 1} := by
  erw [repl, (euclideanSpace.continuousLinearEquiv K).toContinuousLinearMap.frontier_preimage,
    frontier_S_eq, ← repl']
  exact (euclideanSpace.continuousLinearEquiv K).surjective

example :
    volume (frontier {x | x ∈ X K ∧
      mixedEmbedding.norm ((euclideanSpace.linearEquiv K) x) ≤ 1}) = 0 := by
  have := ContinuousLinearMap.frontier_preimage
    (euclideanSpace.continuousLinearEquiv K : (E₂ K) →L[ℝ] (E K))
    (ContinuousLinearEquiv.surjective _)
    (S K)
  erw [euclideanSpace.coe_continuousLinearEquiv, this, MeasurePreserving.measure_preimage
    (measurePreserving_euclideanLinearEquiv K), frontier_S_eq, frontier_ae_null]

  sorry

-- volume (frontier {x | x ∈ X K ∧ mixedEmbedding.norm ((euclideanSpace.linearEquiv K) x) ≤ 1}) = 0

#exit

/-- Docs. -/
abbrev X : Set (E₂ K) := (euclideanSpace.linearEquiv K)⁻¹' (fundamentalCone K)

/-- Docs. -/
abbrev X₁ : Set (E₂ K) := {x ∈ X K | mixedEmbedding.norm (euclideanSpace.linearEquiv K x) ≤ 1}

/-- Docs. -/
abbrev F₁ : Set (E₂ K) := {x ∈ X K | mixedEmbedding.norm (euclideanSpace.linearEquiv K x) = 1}

variable {K}

theorem aux00 {x : E₂ K} (hx : x ∈ X K) :
    0 < mixedEmbedding.norm (euclideanSpace.linearEquiv K x) :=
  lt_iff_le_and_ne.mpr ⟨mixedEmbedding.norm_nonneg _, Ne.symm hx.2⟩

theorem aux0 {x : E₂ K} (hx : x ∈ X₁ K) :
    ∃ c : ℝ, 1 ≤ c ∧ c • x ∈ F₁ K := by
  have : finrank ℚ K ≠ 0 := ne_of_gt finrank_pos
  refine ⟨((mixedEmbedding.norm (euclideanSpace.linearEquiv K x)) ^ (-(finrank ℚ K : ℝ)⁻¹)),
    ?_, ?_⟩
  · refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos ?_ ?_ ?_
    · exact aux00 hx.1
    · exact hx.2
    · aesop
  · refine ⟨?_, ?_⟩
    · rw [X, Set.mem_preimage, _root_.map_smul]
      refine smul_mem_of_mem hx.1 ?_
      refine (Real.rpow_ne_zero ?_ ?_).mpr ?_
      exact mixedEmbedding.norm_nonneg _
      aesop
      exact ne_of_gt (aux00 hx.1)
    · have := aux00 hx.1
      rw [_root_.map_smul, mixedEmbedding.norm_smul, abs_eq_self.mpr]
      rw [← Real.rpow_natCast, ← Real.rpow_mul, neg_mul, inv_mul_cancel, Real.rpow_neg_one,
        inv_mul_cancel]
      exact ne_of_gt (aux00 hx.1)
      aesop
      exact mixedEmbedding.norm_nonneg _
      refine Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _

theorem aux1 (h : IsBounded (F₁ K)) :
    IsBounded (X₁ K) := by
  rw [Metric.isBounded_iff_subset_ball 0]
  obtain ⟨r, hr₁, hr₂⟩ := h.subset_ball_lt 0 0
  refine ⟨r, ?_⟩
  intro x hx
  obtain ⟨c, hc₁, hc₂⟩ := aux0 hx
  have := hr₂ hc₂
  rw [mem_ball_zero_iff] at this ⊢
  rw [← smul_lt_smul_iff_of_pos_left (by linarith : 0 < c)]
  rw [show c • ‖x‖ = ‖c • x‖ by
    rw [norm_smul, Real.norm_eq_abs, abs_eq_self.mpr (by linarith), smul_eq_mul]]
  refine lt_of_lt_of_le this ?_
  refine le_smul_of_one_le_left ?_ ?_
  exact le_of_lt hr₁
  exact hc₁

theorem aux11 : frontier (X₁ K) = F₁ K := by
  unfold X₁ F₁
  let f := Set.indicator (X K)
    (fun x : E₂ K ↦ mixedEmbedding.norm (euclideanSpace.linearEquiv K x))
  let g := Set.indicator (X K) (fun _ ↦ (1 : ℝ))
  have := frontier_le_eq_eq (f := f) (g := g) sorry sorry sorry
  convert this
  · sorry
  · sorry

theorem logMap_apply_F₁_ofIsReal {x : E₂ K} (hx : x ∈ F₁ K) {w : InfinitePlace K} (hw₁ : w ≠ w₀)
    (hw₂ : IsReal w) :
    logMap (euclideanSpace.linearEquiv K x) ⟨w, hw₁⟩ = Real.log ‖x.1 ⟨w, hw₂⟩‖ := by
  rw [logMap, dif_pos hw₂, hx.2, Real.log_one, zero_mul, sub_zero]
  rfl

theorem logMap_apply_F₁_ofIsComplex {x : E₂ K} (hx : x ∈ F₁ K) {w : InfinitePlace K} (hw₁ : w ≠ w₀)
    (hw₂ : IsComplex w) :
    logMap (euclideanSpace.linearEquiv K x) ⟨w, hw₁⟩ = 2 * Real.log ‖x.2 ⟨w, hw₂⟩‖ := by
  rw [logMap, dif_neg (not_isReal_iff_isComplex.mpr hw₂), hx.2, Real.log_one, zero_mul, sub_zero]
  rfl

theorem logMap_bounded_of_mem {w : InfinitePlace K} (hw : w ≠ w₀) :
    ∃ C, ∀ x ∈ fundamentalCone K, ‖logMap x ⟨w, hw⟩‖ ≤ C := by
  classical
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  obtain ⟨r, hr₁, hr₂⟩ := (Zspan.fundamentalDomain_isBounded B).subset_closedBall_lt 0 0
  refine ⟨r, fun _ hx ↦ ?_⟩ -- (pi_norm_le_iff hr₁).mp (mem_closedBall_zero_iff.mp (hr₂ hx.1)) ⟨w, hw⟩⟩
  have := mem_closedBall_zero_iff.mp (hr₂ hx.1)
  sorry

theorem bounded_at_ne_w₀_isReal {w : InfinitePlace K} (hw : IsReal w) (hw' : w ≠ w₀) :
    ∃ C₁ C₂,∀ x ∈ F₁ K, 0 < C₁ ∧ C₁ ≤ ‖x.1 ⟨w, hw⟩‖ ∧ ‖x.1 ⟨w, hw⟩‖ ≤ C₂ := by
  obtain ⟨r, hr⟩ := logMap_bounded_of_mem hw'
  refine ⟨Real.exp (- r), Real.exp r, fun x hx ↦ ⟨Real.exp_pos _, ?_⟩⟩
  rw [← Real.log_le_iff_le_exp, ← Real.le_log_iff_exp_le, ← abs_le]
  sorry
  sorry
  sorry

theorem bounded_at_ne_w₀_isComplex {w : InfinitePlace K} (hw : IsComplex w) (hw' : w ≠ w₀) :
    ∃ C₁ C₂, ∀ x ∈ X K, 0 < C₁ ∧ C₁ ≤ ‖x.2 ⟨w, hw⟩‖ ∧ ‖x.2 ⟨w, hw⟩‖ ≤ C₂ := sorry

theorem bounded_of_mem_F₁_at_w₀_isReal (hw₀ : IsReal w₀) :
    ∃ C, ∀ x ∈ F₁ K, ‖x.1 ⟨w₀, hw₀⟩‖ ≤ C := sorry

theorem bounded_of_mem_F₁_at_w₀_isComplex (hw₀ : IsComplex w₀) :
    ∃ C, ∀ x ∈ F₁ K, ‖x.2 ⟨w₀, hw₀⟩‖ ≤ C := sorry

variable (K)

-- use this:  obtain hw | hw := w.isReal_or_isComplex

theorem bounded_of_mem_F₁_at_index (i : index K) :
    ∃ C, ∀ x ∈ F₁ K, |(euclideanSpace.stdOrthonormalBasis K).repr x i| ≤ C := by
  cases i with
  | inl w =>
      simp only [stdOrthonormalBasis_repr_apply, stdBasis_apply_ofIsReal]
      by_cases hw : w.val = w₀
      · have : IsReal (w₀ : InfinitePlace K) := by
          rw [← hw]
          exact w.prop
        have := bounded_of_mem_F₁_at_w₀_isReal this
        convert this
      · have := bounded_at_ne_w₀_isReal w.prop hw
        obtain ⟨_, C, hC⟩ := this
        refine ⟨C, ?_⟩
        intro _ hx
        exact (hC _ hx).2.2
  | inr wj =>
      rcases wj with ⟨w, j⟩
      by_cases hw : w.val = w₀
      · have : IsComplex (w₀ : InfinitePlace K) := by
          rw [← hw]
          exact w.prop
        obtain ⟨C, hC⟩ := bounded_of_mem_F₁_at_w₀_isComplex this
        fin_cases j
        · refine ⟨C, ?_⟩
          intro _ hx
          refine le_trans (Complex.abs_re_le_abs _) ?_
          convert hC _ hx
        · refine ⟨C, ?_⟩
          intro _ hx
          refine le_trans (Complex.abs_im_le_abs _) ?_
          convert hC _ hx
      · have := bounded_at_ne_w₀_isComplex w.prop hw
        obtain ⟨_, C, hC⟩ := this
        fin_cases j
        · simp only [Fin.zero_eta, stdOrthonormalBasis_repr_apply, Fin.isValue,
            stdBasis_apply_ofIsComplex_fst]
          refine ⟨C, ?_⟩
          intro _ hx
          refine le_trans (Complex.abs_re_le_abs _) ?_
          exact (hC _ hx.1).2.2
        · simp only [Fin.mk_one, stdOrthonormalBasis_repr_apply, Fin.isValue,
            stdBasis_apply_ofIsComplex_snd]
          refine ⟨C, ?_⟩
          intro _ hx
          refine le_trans (Complex.abs_im_le_abs _) ?_
          exact (hC _ hx.1).2.2

theorem aux20 :
    ∃ s : Set ℝ, IsBounded s ∧ ∀ i, ∀ x ∈ F₁ K,
      (euclideanSpace.stdOrthonormalBasis K).repr x i ∈ s := by
  refine ⟨?_, ?_, ?_⟩
  · let R := Finset.univ.sup' ?_ fun i : index K ↦ (bounded_of_mem_F₁_at_index K i).choose
    exact Metric.closedBall 0 R
    exact Finset.univ_nonempty
  · exact Metric.isBounded_closedBall
  · intro i _ hx
    have := (bounded_of_mem_F₁_at_index K i).choose_spec _ hx
    rw [mem_closedBall_zero_iff]
    refine le_trans this ?_
    refine Finset.univ.le_sup' (fun i : index K ↦ (bounded_of_mem_F₁_at_index K i).choose) ?_
    exact Finset.mem_univ i

-- theorem logMap_bounded_of_mem {x : E K} (hx : x ∈ fundamentalCone K) {w : InfinitePlace K}
--     (hw : w ≠ w₀) :
--     ∃ C, ‖logMap x ⟨w, hw⟩‖ < C := by
--   classical
--   let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
--   obtain ⟨r, hr₁, hr₂⟩ := (Zspan.fundamentalDomain_isBounded B).subset_ball_lt 0 0
--   exact ⟨r, (pi_norm_lt_iff hr₁).mp (mem_ball_zero_iff.mp (hr₂ hx.1)) ⟨w, hw⟩⟩

-- theorem aux20 :
--     ∃ s : Set ℝ, IsBounded s ∧ ∀ i, ∀ x ∈ F₁ K,
--       (euclideanSpace.stdOrthonormalBasis K).repr x i ∈ s := by
--   rsuffices ⟨C₁, C₂, hC₁, hC₂, h⟩ : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 1 ≤ C₂ ∧
--       ∀ x ∈ (F₁ K),
--         (∀ w, w.val ≠ w₀ → C₁ < ‖x.1 w‖ ∧ ‖x.1 w‖ ≤ C₂) ∧
--         (∀ w, w.val ≠ w₀ → C₁ < ‖x.2 w‖ ^ 2 ∧ ‖x.2 w‖ ^ 2 ≤ C₂) := by
--     let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
--     obtain ⟨r, hr₁, hr₂⟩ := (Zspan.fundamentalDomain_isBounded B).subset_ball_lt 0 0
--     have h : ∀ x ∈ X K, ∀ w : { w // w ≠ w₀ },
--       ‖logMap ((euclideanSpace.linearEquiv K) x) w‖ < r :=
--         fun _ h ↦ (pi_norm_lt_iff hr₁).mp  <| mem_ball_zero_iff.mp (hr₂ h.1)
--     refine ⟨Real.exp (- r), Real.exp r, Real.exp_pos _, Real.one_le_exp (le_of_lt hr₁),
--       fun x hx ↦ ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩
--     · specialize h x hx.1 ⟨w.val, hw⟩
--       rw [← Real.log_lt_iff_lt_exp, ← Real.lt_log_iff_exp_lt, ← abs_lt]
--       rwa [logMap_apply_F₁_ofIsReal hx hw w.prop, Real.norm_eq_abs] at h
--       sorry
--       sorry
--     · specialize h x hx.1 ⟨w.val, hw⟩
--       rw [← Real.log_lt_iff_lt_exp, ← Real.lt_log_iff_exp_lt, ← abs_lt, Real.log_pow,
--         Nat.cast_ofNat]
--       rwa [logMap_apply_F₁_ofIsComplex hx hw w.prop, Real.norm_eq_abs] at h
--       sorry
--       sorry
--   let M := max C₂ (C₁ ^ (1 - Fintype.card (InfinitePlace K)))
--   refine ⟨Metric.closedBall 0 M, Metric.isBounded_closedBall, fun i x hx  ↦ ?_⟩
--   rw [mem_closedBall_zero_iff]
--   cases i with
--   | inl w =>
--       by_cases hw : w.1 ≠ w₀
--       · rw [stdOrthonormalBasis_repr_apply, stdBasis_apply_ofIsReal]
--         rw [euclideanSpace.linearEquiv_apply_ofIsReal]
--         replace h := ((h x hx).1 w hw).2
--         refine le_trans ?_ (le_max_left _ _)
--         exact h
--       ·
--         sorry
--   | inr wj =>
--       rcases wj with ⟨w, j⟩
--       by_cases hw : w.1 ≠ w₀
--       · fin_cases j
--         · rw [Fin.zero_eta, stdOrthonormalBasis_repr_apply, stdBasis_apply_ofIsComplex_fst,
--             Real.norm_eq_abs]
--           refine le_trans (Complex.abs_re_le_abs _) ?_
--           replace h := ((h x hx).2 w hw).2
--           refine le_trans ?_ (le_max_left _ _)
--           rw [← Real.le_sqrt] at h
--           refine le_trans h ?_
--           sorry
--           exact norm_nonneg _
--           sorry
--         · rw [Fin.mk_one, stdOrthonormalBasis_repr_apply, stdBasis_apply_ofIsComplex_snd,
--             Real.norm_eq_abs]
--           refine le_trans (Complex.abs_im_le_abs _) ?_
--           replace h := ((h x hx).2 w hw).2
--           refine le_trans ?_ (le_max_left _ _)
--           rw [← Real.le_sqrt] at h
--           refine le_trans h ?_
--           sorry
--           exact norm_nonneg _
--           sorry
--       · sorry

  --   let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  --   have := (Zspan.fundamentalDomain_isBounded B).subset_ball_lt 0 0
  --   obtain ⟨r, hr₁, hr₂⟩ := this
  --   refine ⟨Real.exp (- r), Real.exp r, Real.exp_pos _, Real.exp_pos _, fun x hx₁ ↦ ?_⟩
  --   have hx₂ : x ≠ 0 := sorry
  --   have hx₃ : (∀ w, x.1 w ≠ 0) ∧ (∀ w, x.2 w ≠ 0) := sorry
  --   have hx₄ :  ∀ w : { w // w ≠ w₀ }, ‖logMap ((euclideanSpace.linearEquiv K) x) w‖ < r := by
  --     rw [← pi_norm_lt_iff hr₁, ← mem_ball_zero_iff]
  --     refine hr₂ ?_
  --     have := hx₁.1
  --     rw [X, fundamentalCone, Set.mem_preimage] at this
  --     exact (this.resolve_right (by simp [hx₂])).1

theorem aux2 : IsBounded (F₁ K) := by
  obtain ⟨s, hs₁, hs₂⟩ : ∃ s : Set ℝ, IsBounded s ∧ ∀ i, ∀ x ∈ F₁ K,
    (euclideanSpace.stdOrthonormalBasis K).repr x i ∈ s := aux20 K
  refine IsBounded.subset (isBoundedOfBoundedCoeff
    (fun i ↦ euclideanSpace.stdOrthonormalBasis K i) hs₁) ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · intro i
    refine ⟨(euclideanSpace.stdOrthonormalBasis K).repr x i, ?_⟩
    exact hs₂ i x hx
  · simp_rw [OrthonormalBasis.sum_repr]

def iso3 : ↑(↑(Λ K) ∩ X K) ≃ integralPoint K :=
  Equiv.subtypeEquiv (euclideanSpace.linearEquiv _).toEquiv fun x ↦ by
  simp only [Λ, coe_toAddSubgroup, Set.inter_comm _ (X K), Set.mem_inter_iff, Set.mem_preimage,
    SetLike.mem_coe, LinearEquiv.coe_toEquiv, integralPoint, Set.mem_image, Set.mem_range,
    exists_exists_eq_and, and_congr_right_iff]
  intro _
  rw [← Zspan.map]
  rw [Submodule.mem_map]
  simp_rw [mem_span_latticeBasis]
  simp only [RingHom.mem_range, RingHom.coe_comp, Function.comp_apply,
    LinearEquiv.restrictScalars_apply, exists_exists_eq_and]
  simp_rw [LinearEquiv.symm_apply_eq]

@[simp]
theorem iso3_apply (x : ↑(↑(Λ K) ∩ X K)) :
    iso3 K x = euclideanSpace.linearEquiv K (x : E₂ K) := rfl

open Submodule Ideal nonZeroDivisors

example :
    Tendsto (fun n : ℕ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ n} * torsionOrder K : ℝ) / n) atTop
          (𝓝 ((volume (X₁ K)).toReal / Zlattice.covolume (Λ K))) := by
  refine Tendsto.congr' ?_
    (Tendsto.comp (Zlattice.covolume.tendsto_card_le_div' (Λ K) ?_ ?_ ?_ ?_)
      tendsto_natCast_atTop_atTop)
  · filter_upwards with n
    have := card_isPrincipal_norm_le K n
    simp_rw [Function.comp_apply, ← Nat.cast_mul]
    rw [this]
    simp_rw [Set.setOf_inter_eq_sep, ← and_assoc, ← Set.mem_inter_iff]
    congr 2
    refine Nat.card_congr ?_
    refine Equiv.trans (Equiv.Set.sep _ _) ?_
    refine Equiv.subtypeEquiv (iso3 K) ?_
    intro x
    simp_rw [Set.mem_setOf_eq, ← Nat.cast_le (α := ℝ), intNorm_coe]
    have := iso3_apply K x
    rw [this]
  · intro x c hx hc
    sorry
  · intro x r hr
    rw [LinearMapClass.map_smul, mixedEmbedding.norm_smul, euclideanSpace.finrank,
      abs_eq_self.mpr hr.le]
  · refine aux1 ?_
    exact aux2 K
  ·
    sorry

#exit

example :
    Tendsto (fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) | Submodule.IsPrincipal I ∧ Ideal.absNorm I ∈ Finset.Icc 1 n} *
        torsionOrder K : ℝ) / n) atTop
          (𝓝 ((volume (X₁ K)).toReal / Zlattice.covolume (Λ K))) := by
  refine Tendsto.congr' ?_
--  refine IsEquivalent.tendsto_nhds ?_
    (Tendsto.comp (Zlattice.covolume.tendsto_card_le_div' (Λ K) ?_ ?_ ?_ ?_)
      tendsto_natCast_atTop_atTop)
  · have := card_isPrincipal_norm_le_div_atTop K
    refine IsEquivalent.trans ?_ this.symm
    refine EventuallyEq.isEquivalent ?_
    filter_upwards with _
    simp_rw [Function.comp_apply, Set.setOf_inter_eq_sep, ← and_assoc, ← Set.mem_inter_iff]
    -- have := card_isPrincipal_norm_in_Icc K c
    -- simp_rw [this]
    congr 2
    refine Nat.card_congr ?_
    refine Equiv.trans (Equiv.Set.sep _ _) ?_
    refine Equiv.subtypeEquiv (iso3 K) ?_
    intro x
    simp_rw [Set.mem_setOf_eq, ← Nat.cast_le (α := ℝ), intNorm_coe]
    have := iso3_apply x
    rw [this]
  · intro x r hx hr
    erw [Set.mem_preimage, _root_.map_smul (euclideanSpace.linearEquiv K)]
    refine smul_mem_of_mem ?_ r
    exact hx
  · intro x r hr
    rw [_root_.map_smul, mixedEmbedding.norm_smul, abs_eq_self.mpr hr]
    erw [mixedEmbedding.finrank]
  · -- Not trivial at all
    sorry
  · refine MeasurableSet.inter ?_ ?_
    · rw [X]
      refine measurableSet_preimage (euclideanSpace.homeomorph K).measurable ?_
      sorry
    · refine measurableSet_le (f := fun x ↦ mixedEmbedding.norm (euclideanSpace.linearEquiv K x))
        (g := fun _ ↦ 1) ?_ ?_
      sorry
      exact measurable_const

#lint
