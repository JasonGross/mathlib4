/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Patrick Massot
-/
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Separation
import Mathlib.Topology.DenseEmbedding

/-!
# Uniform embeddings of uniform spaces.

Extension of uniform continuous functions.
-/


open Filter Function Set Uniformity Topology

section

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w} [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-!
### Uniform inducing maps
-/

/-- A map `f : α → β` between uniform spaces is called *uniform inducing* if the uniformity filter
on `α` is the pullback of the uniformity filter on `β` under `Prod.map f f`. If `α` is a separated
space, then this implies that `f` is injective, hence it is a `UniformEmbedding`. -/
@[mk_iff]
structure UniformInducing (f : α → β) : Prop where
  /-- The uniformity filter on the domain is the pullback of the uniformity filter on the codomain
  under `Prod.map f f`. -/
  comap_uniformity : comap (fun x : α × α => (f x.1, f x.2)) (𝓤 β) = 𝓤 α

lemma uniformInducing_iff_uniformSpace {f : α → β} :
    UniformInducing f ↔ ‹UniformSpace β›.comap f = ‹UniformSpace α› := by
  rw [uniformInducing_iff, UniformSpace.ext_iff, Filter.ext_iff]
  rfl

protected alias ⟨UniformInducing.comap_uniformSpace, _⟩ := uniformInducing_iff_uniformSpace

lemma uniformInducing_iff' {f : α → β} :
    UniformInducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) ≤ 𝓤 α := by
  rw [uniformInducing_iff, UniformContinuous, tendsto_iff_comap, le_antisymm_iff, and_comm]; rfl

protected lemma Filter.HasBasis.uniformInducing_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    UniformInducing f ↔
      (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
        (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) := by
  simp [uniformInducing_iff', h.uniformContinuous_iff h', (h'.comap _).le_basis_iff h, subset_def]

theorem UniformInducing.mk' {f : α → β}
    (h : ∀ s, s ∈ 𝓤 α ↔ ∃ t ∈ 𝓤 β, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s) : UniformInducing f :=
  ⟨by simp [eq_comm, Filter.ext_iff, subset_def, h]⟩

theorem uniformInducing_id : UniformInducing (@id α) :=
  ⟨by rw [← Prod.map_def, Prod.map_id, comap_id]⟩

theorem UniformInducing.comp {g : β → γ} (hg : UniformInducing g) {f : α → β}
    (hf : UniformInducing f) : UniformInducing (g ∘ f) :=
  ⟨by rw [← hf.1, ← hg.1, comap_comap]; rfl⟩

theorem UniformInducing.of_comp_iff {g : β → γ} (hg : UniformInducing g) {f : α → β} :
    UniformInducing (g ∘ f) ↔ UniformInducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [uniformInducing_iff, ← hg.comap_uniformity, comap_comap, ← h.comap_uniformity,
    Function.comp_def, Function.comp_def]

theorem UniformInducing.basis_uniformity {f : α → β} (hf : UniformInducing f) {ι : Sort*}
    {p : ι → Prop} {s : ι → Set (β × β)} (H : (𝓤 β).HasBasis p s) :
    (𝓤 α).HasBasis p fun i => Prod.map f f ⁻¹' s i :=
  hf.1 ▸ H.comap _

theorem UniformInducing.cauchy_map_iff {f : α → β} (hf : UniformInducing f) {F : Filter α} :
    Cauchy (map f F) ↔ Cauchy F := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap, ← hf.comap_uniformity]

theorem uniformInducing_of_compose {f : α → β} {g : β → γ} (hf : UniformContinuous f)
    (hg : UniformContinuous g) (hgf : UniformInducing (g ∘ f)) : UniformInducing f := by
  refine ⟨le_antisymm ?_ hf.le_comap⟩
  rw [← hgf.1, ← Prod.map_def, ← Prod.map_def, ← Prod.map_comp_map f f g g, ← comap_comap]
  exact comap_mono hg.le_comap

theorem UniformInducing.uniformContinuous {f : α → β} (hf : UniformInducing f) :
    UniformContinuous f := (uniformInducing_iff'.1 hf).1

theorem UniformInducing.uniformContinuous_iff {f : α → β} {g : β → γ} (hg : UniformInducing g) :
    UniformContinuous f ↔ UniformContinuous (g ∘ f) := by
  dsimp only [UniformContinuous, Tendsto]
  simp only [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map, Function.comp_def]

protected theorem UniformInducing.uniformInducing_comp_iff {f : α → β} {g : β → γ}
    (hg : UniformInducing g) : UniformInducing (g ∘ f) ↔ UniformInducing f := by
  simp only [uniformInducing_iff, ← hg.comap_uniformity, comap_comap, Function.comp_def]

theorem UniformInducing.uniformContinuousOn_iff {f : α → β} {g : β → γ} {S : Set α}
    (hg : UniformInducing g) :
    UniformContinuousOn f S ↔ UniformContinuousOn (g ∘ f) S := by
  dsimp only [UniformContinuousOn, Tendsto]
  rw [← hg.comap_uniformity, ← map_le_iff_le_comap, Filter.map_map, comp_def, comp_def]

theorem UniformInducing.inducing {f : α → β} (h : UniformInducing f) : Inducing f := by
  obtain rfl := h.comap_uniformSpace
  exact inducing_induced f

theorem UniformInducing.prod {α' : Type*} {β' : Type*} [UniformSpace α'] [UniformSpace β']
    {e₁ : α → α'} {e₂ : β → β'} (h₁ : UniformInducing e₁) (h₂ : UniformInducing e₂) :
    UniformInducing fun p : α × β => (e₁ p.1, e₂ p.2) :=
  ⟨by simp [Function.comp_def, uniformity_prod, ← h₁.1, ← h₂.1, comap_inf, comap_comap]⟩

theorem UniformInducing.isDenseInducing {f : α → β} (h : UniformInducing f) (hd : DenseRange f) :
    IsDenseInducing f :=
  { dense := hd
    induced := h.inducing.induced }

theorem SeparationQuotient.uniformInducing_mk : UniformInducing (mk : α → SeparationQuotient α) :=
  ⟨comap_mk_uniformity⟩

protected theorem UniformInducing.injective [T0Space α] {f : α → β} (h : UniformInducing f) :
    Injective f :=
  h.inducing.injective

/-!
### Uniform embeddings
-/

/-- A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and
injective. If `α` is a separated space, then the latter assumption follows from the former. -/
@[mk_iff]
structure UniformEmbedding (f : α → β) extends UniformInducing f : Prop where
  /-- A uniform embedding is injective. -/
  inj : Function.Injective f

theorem uniformEmbedding_iff' {f : α → β} :
    UniformEmbedding f ↔ Injective f ∧ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) ≤ 𝓤 α := by
  rw [uniformEmbedding_iff, and_comm, uniformInducing_iff']

theorem Filter.HasBasis.uniformEmbedding_iff' {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    UniformEmbedding f ↔ Injective f ∧
      (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
        (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) := by
  rw [uniformEmbedding_iff, and_comm, h.uniformInducing_iff h']

theorem Filter.HasBasis.uniformEmbedding_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
    (h : (𝓤 α).HasBasis p s) (h' : (𝓤 β).HasBasis p' s') {f : α → β} :
    UniformEmbedding f ↔ Injective f ∧ UniformContinuous f ∧
      (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) := by
  simp only [h.uniformEmbedding_iff' h', h.uniformContinuous_iff h']

theorem uniformEmbedding_subtype_val {p : α → Prop} :
    UniformEmbedding (Subtype.val : Subtype p → α) :=
  { comap_uniformity := rfl
    inj := Subtype.val_injective }

theorem uniformEmbedding_set_inclusion {s t : Set α} (hst : s ⊆ t) :
    UniformEmbedding (inclusion hst) where
  comap_uniformity := by rw [uniformity_subtype, uniformity_subtype, comap_comap]; rfl
  inj := inclusion_injective hst

theorem UniformEmbedding.comp {g : β → γ} (hg : UniformEmbedding g) {f : α → β}
    (hf : UniformEmbedding f) : UniformEmbedding (g ∘ f) :=
  { hg.toUniformInducing.comp hf.toUniformInducing with inj := hg.inj.comp hf.inj }

theorem UniformEmbedding.of_comp_iff {g : β → γ} (hg : UniformEmbedding g) {f : α → β} :
    UniformEmbedding (g ∘ f) ↔ UniformEmbedding f := by
  simp_rw [uniformEmbedding_iff, hg.toUniformInducing.of_comp_iff, hg.inj.of_comp_iff f]

theorem Equiv.uniformEmbedding {α β : Type*} [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (h₁ : UniformContinuous f) (h₂ : UniformContinuous f.symm) : UniformEmbedding f :=
  uniformEmbedding_iff'.2 ⟨f.injective, h₁, by rwa [← Equiv.prodCongr_apply, ← map_equiv_symm]⟩

theorem uniformEmbedding_inl : UniformEmbedding (Sum.inl : α → α ⊕ β) :=
  uniformEmbedding_iff'.2 ⟨Sum.inl_injective, uniformContinuous_inl, fun s hs =>
    ⟨Prod.map Sum.inl Sum.inl '' s ∪ range (Prod.map Sum.inr Sum.inr),
      union_mem_sup (image_mem_map hs) range_mem_map,
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

theorem uniformEmbedding_inr : UniformEmbedding (Sum.inr : β → α ⊕ β) :=
  uniformEmbedding_iff'.2 ⟨Sum.inr_injective, uniformContinuous_inr, fun s hs =>
    ⟨range (Prod.map Sum.inl Sum.inl) ∪ Prod.map Sum.inr Sum.inr '' s,
      union_mem_sup range_mem_map (image_mem_map hs),
      fun x h => by simpa [Prod.map_apply'] using h⟩⟩

/-- If the domain of a `UniformInducing` map `f` is a T₀ space, then `f` is injective,
hence it is a `UniformEmbedding`. -/
protected theorem UniformInducing.uniformEmbedding [T0Space α] {f : α → β}
    (hf : UniformInducing f) : UniformEmbedding f :=
  ⟨hf, hf.inducing.injective⟩

theorem uniformEmbedding_iff_uniformInducing [T0Space α] {f : α → β} :
    UniformEmbedding f ↔ UniformInducing f :=
  ⟨UniformEmbedding.toUniformInducing, UniformInducing.uniformEmbedding⟩

/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is uniform inducing with respect to the discrete uniformity on `α`:
the preimage of `𝓤 β` under `Prod.map f f` is the principal filter generated by the diagonal in
`α × α`. -/
theorem comap_uniformity_of_spaced_out {α} {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : comap (Prod.map f f) (𝓤 β) = 𝓟 idRel := by
  refine le_antisymm ?_ (@refl_le_uniformity α (UniformSpace.comap f _))
  calc
    comap (Prod.map f f) (𝓤 β) ≤ comap (Prod.map f f) (𝓟 s) := comap_mono (le_principal_iff.2 hs)
    _ = 𝓟 (Prod.map f f ⁻¹' s) := comap_principal
    _ ≤ 𝓟 idRel := principal_mono.2 ?_
  rintro ⟨x, y⟩; simpa [not_imp_not] using @hf x y

/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is a uniform embedding with respect to the discrete uniformity on `α`. -/
theorem uniformEmbedding_of_spaced_out {α} {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : @UniformEmbedding α β ⊥ ‹_› f := by
  let _ : UniformSpace α := ⊥; have := discreteTopology_bot α
  exact UniformInducing.uniformEmbedding ⟨comap_uniformity_of_spaced_out hs hf⟩

protected theorem UniformEmbedding.embedding {f : α → β} (h : UniformEmbedding f) : Embedding f :=
  { toInducing := h.toUniformInducing.inducing
    inj := h.inj }

theorem UniformEmbedding.denseEmbedding {f : α → β} (h : UniformEmbedding f) (hd : DenseRange f) :
    DenseEmbedding f :=
  { h.embedding with dense := hd }

theorem closedEmbedding_of_spaced_out {α} [TopologicalSpace α] [DiscreteTopology α]
    [T0Space β] {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
    (hf : Pairwise fun x y => (f x, f y) ∉ s) : ClosedEmbedding f := by
  rcases @DiscreteTopology.eq_bot α _ _ with rfl; let _ : UniformSpace α := ⊥
  exact
    { (uniformEmbedding_of_spaced_out hs hf).embedding with
      isClosed_range := isClosed_range_of_spaced_out hs hf }

theorem closure_image_mem_nhds_of_uniformInducing {s : Set (α × α)} {e : α → β} (b : β)
    (he₁ : UniformInducing e) (he₂ : IsDenseInducing e) (hs : s ∈ 𝓤 α) :
    ∃ a, closure (e '' { a' | (a, a') ∈ s }) ∈ 𝓝 b := by
  obtain ⟨U, ⟨hU, hUo, hsymm⟩, hs⟩ :
    ∃ U, (U ∈ 𝓤 β ∧ IsOpen U ∧ SymmetricRel U) ∧ Prod.map e e ⁻¹' U ⊆ s := by
      rwa [← he₁.comap_uniformity, (uniformity_hasBasis_open_symmetric.comap _).mem_iff] at hs
  rcases he₂.dense.mem_nhds (UniformSpace.ball_mem_nhds b hU) with ⟨a, ha⟩
  refine ⟨a, mem_of_superset ?_ (closure_mono <| image_subset _ <| UniformSpace.ball_mono hs a)⟩
  have ho : IsOpen (UniformSpace.ball (e a) U) := UniformSpace.isOpen_ball (e a) hUo
  refine mem_of_superset (ho.mem_nhds <| (UniformSpace.mem_ball_symmetry hsymm).2 ha) fun y hy => ?_
  refine mem_closure_iff_nhds.2 fun V hV => ?_
  rcases he₂.dense.mem_nhds (inter_mem hV (ho.mem_nhds hy)) with ⟨x, hxV, hxU⟩
  exact ⟨e x, hxV, mem_image_of_mem e hxU⟩

theorem uniformEmbedding_subtypeEmb (p : α → Prop) {e : α → β} (ue : UniformEmbedding e)
    (de : DenseEmbedding e) : UniformEmbedding (DenseEmbedding.subtypeEmb p e) :=
  { comap_uniformity := by
      simp [comap_comap, Function.comp_def, DenseEmbedding.subtypeEmb, uniformity_subtype,
        ue.comap_uniformity.symm]
    inj := (de.subtype p).inj }

theorem UniformEmbedding.prod {α' : Type*} {β' : Type*} [UniformSpace α'] [UniformSpace β']
    {e₁ : α → α'} {e₂ : β → β'} (h₁ : UniformEmbedding e₁) (h₂ : UniformEmbedding e₂) :
    UniformEmbedding fun p : α × β => (e₁ p.1, e₂ p.2) :=
  { h₁.toUniformInducing.prod h₂.toUniformInducing with inj := h₁.inj.prodMap h₂.inj }

/-- A set is complete iff its image under a uniform inducing map is complete. -/
theorem isComplete_image_iff {m : α → β} {s : Set α} (hm : UniformInducing m) :
    IsComplete (m '' s) ↔ IsComplete s := by
  have fact1 : SurjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := surjOn_image .. |>.filter_map_Iic
  have fact2 : MapsTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 <| m '' s) := mapsTo_image .. |>.filter_map_Iic
  simp_rw [IsComplete, imp.swap (a := Cauchy _), ← mem_Iic (b := 𝓟 _), fact1.forall fact2,
    hm.cauchy_map_iff, exists_mem_image, map_le_iff_le_comap, hm.inducing.nhds_eq_comap]

/-- If `f : X → Y` is an `UniformInducing` map, the image `f '' s` of a set `s` is complete
  if and only if `s` is complete. -/
theorem UniformInducing.isComplete_iff {f : α → β} {s : Set α} (hf : UniformInducing f) :
    IsComplete (f '' s) ↔ IsComplete s := isComplete_image_iff hf

/-- If `f : X → Y` is an `UniformEmbedding`, the image `f '' s` of a set `s` is complete
  if and only if `s` is complete. -/
theorem UniformEmbedding.isComplete_iff {f : α → β} {s : Set α} (hf : UniformEmbedding f) :
    IsComplete (f '' s) ↔ IsComplete s := hf.toUniformInducing.isComplete_iff

/-- Sets of a subtype are complete iff their image under the coercion is complete. -/
theorem Subtype.isComplete_iff {p : α → Prop} {s : Set { x // p x }} :
    IsComplete s ↔ IsComplete ((↑) '' s : Set α) :=
  uniformEmbedding_subtype_val.isComplete_iff.symm

alias ⟨isComplete_of_complete_image, _⟩ := isComplete_image_iff

theorem completeSpace_iff_isComplete_range {f : α → β} (hf : UniformInducing f) :
    CompleteSpace α ↔ IsComplete (range f) := by
  rw [completeSpace_iff_isComplete_univ, ← isComplete_image_iff hf, image_univ]

alias ⟨_, UniformInducing.completeSpace⟩ := completeSpace_iff_isComplete_range

theorem UniformInducing.isComplete_range [CompleteSpace α] {f : α → β} (hf : UniformInducing f) :
    IsComplete (range f) :=
  (completeSpace_iff_isComplete_range hf).1 ‹_›

/-- If `f` is a surjective uniform inducing map,
then its domain is a complete space iff its codomain is a complete space.
See also `_root_.completeSpace_congr` for a version that assumes `f` to be an equivalence. -/
theorem UniformInducing.completeSpace_congr {f : α → β} (hf : UniformInducing f)
    (hsurj : f.Surjective) : CompleteSpace α ↔ CompleteSpace β := by
  rw [completeSpace_iff_isComplete_range hf, hsurj.range_eq, completeSpace_iff_isComplete_univ]

theorem SeparationQuotient.completeSpace_iff :
    CompleteSpace (SeparationQuotient α) ↔ CompleteSpace α :=
  .symm <| uniformInducing_mk.completeSpace_congr surjective_mk

instance SeparationQuotient.instCompleteSpace [CompleteSpace α] :
    CompleteSpace (SeparationQuotient α) :=
  completeSpace_iff.2 ‹_›

/-- See also `UniformInducing.completeSpace_congr`
for a version that works for non-injective maps. -/
theorem completeSpace_congr {e : α ≃ β} (he : UniformEmbedding e) :
    CompleteSpace α ↔ CompleteSpace β :=
  he.completeSpace_congr e.surjective

theorem completeSpace_coe_iff_isComplete {s : Set α} : CompleteSpace s ↔ IsComplete s := by
  rw [completeSpace_iff_isComplete_range uniformEmbedding_subtype_val.toUniformInducing,
    Subtype.range_coe]

alias ⟨_, IsComplete.completeSpace_coe⟩ := completeSpace_coe_iff_isComplete

theorem IsClosed.completeSpace_coe [CompleteSpace α] {s : Set α} (hs : IsClosed s) :
    CompleteSpace s :=
  hs.isComplete.completeSpace_coe

theorem completeSpace_ulift_iff : CompleteSpace (ULift α) ↔ CompleteSpace α :=
  UniformInducing.completeSpace_congr ⟨rfl⟩ ULift.down_surjective

/-- The lift of a complete space to another universe is still complete. -/
instance ULift.instCompleteSpace [CompleteSpace α] : CompleteSpace (ULift α) :=
  completeSpace_ulift_iff.2 ‹_›

theorem completeSpace_extension {m : β → α} (hm : UniformInducing m) (dense : DenseRange m)
    (h : ∀ f : Filter β, Cauchy f → ∃ x : α, map m f ≤ 𝓝 x) : CompleteSpace α :=
  ⟨fun {f : Filter α} (hf : Cauchy f) =>
    let p : Set (α × α) → Set α → Set α := fun s t => { y : α | ∃ x : α, x ∈ t ∧ (x, y) ∈ s }
    let g := (𝓤 α).lift fun s => f.lift' (p s)
    have mp₀ : Monotone p := fun a b h t s ⟨x, xs, xa⟩ => ⟨x, xs, h xa⟩
    have mp₁ : ∀ {s}, Monotone (p s) := fun h x ⟨y, ya, yxs⟩ => ⟨y, h ya, yxs⟩
    have : f ≤ g := le_iInf₂ fun s hs => le_iInf₂ fun t ht =>
      le_principal_iff.mpr <| mem_of_superset ht fun x hx => ⟨x, hx, refl_mem_uniformity hs⟩
    have : NeBot g := hf.left.mono this
    have : NeBot (comap m g) :=
      comap_neBot fun t ht =>
        let ⟨t', ht', ht_mem⟩ := (mem_lift_sets <| monotone_lift' monotone_const mp₀).mp ht
        let ⟨t'', ht'', ht'_sub⟩ := (mem_lift'_sets mp₁).mp ht_mem
        let ⟨x, (hx : x ∈ t'')⟩ := hf.left.nonempty_of_mem ht''
        have h₀ : NeBot (𝓝[range m] x) := dense.nhdsWithin_neBot x
        have h₁ : { y | (x, y) ∈ t' } ∈ 𝓝[range m] x :=
          @mem_inf_of_left α (𝓝 x) (𝓟 (range m)) _ <| mem_nhds_left x ht'
        have h₂ : range m ∈ 𝓝[range m] x :=
          @mem_inf_of_right α (𝓝 x) (𝓟 (range m)) _ <| Subset.refl _
        have : { y | (x, y) ∈ t' } ∩ range m ∈ 𝓝[range m] x := @inter_mem α (𝓝[range m] x) _ _ h₁ h₂
        let ⟨y, xyt', b, b_eq⟩ := h₀.nonempty_of_mem this
        ⟨b, b_eq.symm ▸ ht'_sub ⟨x, hx, xyt'⟩⟩
    have : Cauchy g :=
      ⟨‹NeBot g›, fun s hs =>
        let ⟨s₁, hs₁, (comp_s₁ : compRel s₁ s₁ ⊆ s)⟩ := comp_mem_uniformity_sets hs
        let ⟨s₂, hs₂, (comp_s₂ : compRel s₂ s₂ ⊆ s₁)⟩ := comp_mem_uniformity_sets hs₁
        let ⟨t, ht, (prod_t : t ×ˢ t ⊆ s₂)⟩ := mem_prod_same_iff.mp (hf.right hs₂)
        have hg₁ : p (preimage Prod.swap s₁) t ∈ g :=
          mem_lift (symm_le_uniformity hs₁) <| @mem_lift' α α f _ t ht
        have hg₂ : p s₂ t ∈ g := mem_lift hs₂ <| @mem_lift' α α f _ t ht
        have hg : p (Prod.swap ⁻¹' s₁) t ×ˢ p s₂ t ∈ g ×ˢ g := @prod_mem_prod α α _ _ g g hg₁ hg₂
        (g ×ˢ g).sets_of_superset hg fun ⟨a, b⟩ ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩ =>
          have : (c₁, c₂) ∈ t ×ˢ t := ⟨c₁t, c₂t⟩
          comp_s₁ <| prod_mk_mem_compRel hc₁ <| comp_s₂ <| prod_mk_mem_compRel (prod_t this) hc₂⟩
    have : Cauchy (Filter.comap m g) := ‹Cauchy g›.comap' (le_of_eq hm.comap_uniformity) ‹_›
    let ⟨x, (hx : map m (Filter.comap m g) ≤ 𝓝 x)⟩ := h _ this
    have : ClusterPt x (map m (Filter.comap m g)) :=
      (le_nhds_iff_adhp_of_cauchy (this.map hm.uniformContinuous)).mp hx
    have : ClusterPt x g := this.mono map_comap_le
    ⟨x,
      calc
        f ≤ g := by assumption
        _ ≤ 𝓝 x := le_nhds_of_cauchy_adhp ‹Cauchy g› this
        ⟩⟩

lemma totallyBounded_image_iff {f : α → β} {s : Set α} (hf : UniformInducing f) :
    TotallyBounded (f '' s) ↔ TotallyBounded s := by
  refine ⟨fun hs ↦ ?_, fun h ↦ h.image hf.uniformContinuous⟩
  simp_rw [(hf.basis_uniformity (basis_sets _)).totallyBounded_iff]
  intro t ht
  rcases exists_subset_image_finite_and.1 (hs.exists_subset ht) with ⟨u, -, hfin, h⟩
  use u, hfin
  rwa [biUnion_image, image_subset_iff, preimage_iUnion₂] at h

theorem totallyBounded_preimage {f : α → β} {s : Set β} (hf : UniformInducing f)
    (hs : TotallyBounded s) : TotallyBounded (f ⁻¹' s) :=
  (totallyBounded_image_iff hf).1 <| hs.subset <| image_preimage_subset ..

instance CompleteSpace.sum [CompleteSpace α] [CompleteSpace β] : CompleteSpace (α ⊕ β) := by
  rw [completeSpace_iff_isComplete_univ, ← range_inl_union_range_inr]
  exact uniformEmbedding_inl.toUniformInducing.isComplete_range.union
    uniformEmbedding_inr.toUniformInducing.isComplete_range

end

theorem uniformEmbedding_comap {α : Type*} {β : Type*} {f : α → β} [u : UniformSpace β]
    (hf : Function.Injective f) : @UniformEmbedding α β (UniformSpace.comap f u) u f :=
  @UniformEmbedding.mk _ _ (UniformSpace.comap f u) _ _
    (@UniformInducing.mk _ _ (UniformSpace.comap f u) _ _ rfl) hf

/-- Pull back a uniform space structure by an embedding, adjusting the new uniform structure to
make sure that its topology is defeq to the original one. -/
def Embedding.comapUniformSpace {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α → β)
    (h : Embedding f) : UniformSpace α :=
  (u.comap f).replaceTopology h.induced

theorem Embedding.to_uniformEmbedding {α β} [TopologicalSpace α] [u : UniformSpace β] (f : α → β)
    (h : Embedding f) : @UniformEmbedding α β (h.comapUniformSpace f) u f :=
  let _ := h.comapUniformSpace f
  { comap_uniformity := rfl
    inj := h.inj }

section UniformExtension

variable {α : Type*} {β : Type*} {γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]
  {e : β → α} (h_e : UniformInducing e) (h_dense : DenseRange e) {f : β → γ}
  (h_f : UniformContinuous f)

local notation "ψ" => IsDenseInducing.extend (UniformInducing.isDenseInducing h_e h_dense) f

include h_e h_dense h_f in
theorem uniformly_extend_exists [CompleteSpace γ] (a : α) : ∃ c, Tendsto f (comap e (𝓝 a)) (𝓝 c) :=
  let de := h_e.isDenseInducing h_dense
  have : Cauchy (𝓝 a) := cauchy_nhds
  have : Cauchy (comap e (𝓝 a)) :=
    this.comap' (le_of_eq h_e.comap_uniformity) (de.comap_nhds_neBot _)
  have : Cauchy (map f (comap e (𝓝 a))) := this.map h_f
  CompleteSpace.complete this

theorem uniform_extend_subtype [CompleteSpace γ] {p : α → Prop} {e : α → β} {f : α → γ} {b : β}
    {s : Set α} (hf : UniformContinuous fun x : Subtype p => f x.val) (he : UniformEmbedding e)
    (hd : ∀ x : β, x ∈ closure (range e)) (hb : closure (e '' s) ∈ 𝓝 b) (hs : IsClosed s)
    (hp : ∀ x ∈ s, p x) : ∃ c, Tendsto f (comap e (𝓝 b)) (𝓝 c) := by
  have de : DenseEmbedding e := he.denseEmbedding hd
  have de' : DenseEmbedding (DenseEmbedding.subtypeEmb p e) := de.subtype p
  have ue' : UniformEmbedding (DenseEmbedding.subtypeEmb p e) := uniformEmbedding_subtypeEmb _ he de
  have : b ∈ closure (e '' { x | p x }) :=
    (closure_mono <| monotone_image <| hp) (mem_of_mem_nhds hb)
  let ⟨c, hc⟩ := uniformly_extend_exists ue'.toUniformInducing de'.dense hf ⟨b, this⟩
  replace hc : Tendsto (f ∘ Subtype.val (p := p)) (((𝓝 b).comap e).comap Subtype.val) (𝓝 c) := by
    simpa only [nhds_subtype_eq_comap, comap_comap, DenseEmbedding.subtypeEmb_coe] using hc
  refine ⟨c, (tendsto_comap'_iff ?_).1 hc⟩
  rw [Subtype.range_coe_subtype]
  exact ⟨_, hb, by rwa [← de.toInducing.closure_eq_preimage_closure_image, hs.closure_eq]⟩

include h_e h_f in
theorem uniformly_extend_spec [CompleteSpace γ] (a : α) : Tendsto f (comap e (𝓝 a)) (𝓝 (ψ a)) := by
  simpa only [IsDenseInducing.extend] using
    tendsto_nhds_limUnder (uniformly_extend_exists h_e ‹_› h_f _)

include h_f in
theorem uniformContinuous_uniformly_extend [CompleteSpace γ] : UniformContinuous ψ := fun d hd =>
  let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
  have h_pnt : ∀ {a m}, m ∈ 𝓝 a → ∃ c ∈ f '' (e ⁻¹' m), (c, ψ a) ∈ s ∧ (ψ a, c) ∈ s :=
    fun {a m} hm =>
    have nb : NeBot (map f (comap e (𝓝 a))) :=
      ((h_e.isDenseInducing h_dense).comap_nhds_neBot _).map _
    have :
      f '' (e ⁻¹' m) ∩ ({ c | (c, ψ a) ∈ s } ∩ { c | (ψ a, c) ∈ s }) ∈ map f (comap e (𝓝 a)) :=
      inter_mem (image_mem_map <| preimage_mem_comap <| hm)
        (uniformly_extend_spec h_e h_dense h_f _
          (inter_mem (mem_nhds_right _ hs) (mem_nhds_left _ hs)))
    nb.nonempty_of_mem this
  have : (Prod.map f f) ⁻¹' s ∈ 𝓤 β := h_f hs
  have : (Prod.map f f) ⁻¹' s ∈ comap (Prod.map e e) (𝓤 α) := by
    rwa [← h_e.comap_uniformity] at this
  let ⟨t, ht, ts⟩ := this
  show (Prod.map ψ ψ) ⁻¹' d ∈ 𝓤 α from
    mem_of_superset (interior_mem_uniformity ht) fun ⟨x₁, x₂⟩ hx_t => by
      have : interior t ∈ 𝓝 (x₁, x₂) := isOpen_interior.mem_nhds hx_t
      let ⟨m₁, hm₁, m₂, hm₂, (hm : m₁ ×ˢ m₂ ⊆ interior t)⟩ := mem_nhds_prod_iff.mp this
      obtain ⟨_, ⟨a, ha₁, rfl⟩, _, ha₂⟩ := h_pnt hm₁
      obtain ⟨_, ⟨b, hb₁, rfl⟩, hb₂, _⟩ := h_pnt hm₂
      have : Prod.map f f (a, b) ∈ s :=
        ts <| mem_preimage.2 <| interior_subset (@hm (e a, e b) ⟨ha₁, hb₁⟩)
      exact hs_comp ⟨f a, ha₂, ⟨f b, this, hb₂⟩⟩

variable [T0Space γ]

include h_f in
theorem uniformly_extend_of_ind (b : β) : ψ (e b) = f b :=
  IsDenseInducing.extend_eq_at _ h_f.continuous.continuousAt

theorem uniformly_extend_unique {g : α → γ} (hg : ∀ b, g (e b) = f b) (hc : Continuous g) : ψ = g :=
  IsDenseInducing.extend_unique _ hg hc

end UniformExtension
