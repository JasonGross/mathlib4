import Mathlib.SetTheory.SmallSet
import Mathlib.SetTheory.Ordinal.Basic

universe u v

-- Note to reviewer: Is there a standard identifier for edge labels? (e.g. in graph theory?)
/-- `PreWFTree.{u} η` is the type of well-founded trees with edges labelled by `η`
  and children indexed by arbitrary types in `u`.

Unlike `WFTree`, `PreWFTree` is sensitive to the order and multiplicity of children.
In other words, `PreWFTree` is to `WFTree` as `List` is to `Finset`.-/
inductive PreWFTree (η : Type v) : Type (max (u + 1) v) where
  | mk : (ι : Type u) → (ι → η × PreWFTree η) → PreWFTree η

-- TODO: attempt definition via WellFounded.fix

namespace PreWFTree

variable {η : Type v}

-- abbrev Index : PreWFTree.{u} η → η → Type u
--   | ⟨f⟩, e => (f e).1

-- abbrev child : (t : PreWFTree.{u} η) → (e : η) → t.Index e → PreWFTree.{u} η
--   | ⟨f⟩, e, i => (f e).2 i

-- noncomputable def children' (t : PreWFTree.{u} η) (e : η) : SmallSet.{u} (PreWFTree.{u} η) :=
--   SmallSet.range (t.child e)

-- noncomputable def ofChildren' (f : η → SmallSet.{u} (PreWFTree.{u} η)) : PreWFTree.{u} η :=
--   ⟨fun e ↦ ⟨Shrink.{u} (f e), fun x ↦ (equivShrink (f e)).symm x⟩⟩

-- @[simp]
-- lemma children'_ofChildren' (f : η → SmallSet.{u} (PreWFTree.{u} η)) :
--     children' (ofChildren' f) = f := by
--   ext e
--   simp only [children', ofChildren', SmallSet.mem_range, child]
--   refine ⟨fun ⟨i, h⟩ ↦ ?_, fun h ↦ ?_⟩
--   · generalize ht : (equivShrink ↥(f e)).symm i = t
--     rw [ht] at h
--     subst h
--     simp
--   · use (equivShrink (f e)) ⟨_, h⟩
--     simp

-- Not true!
-- @[simp]
-- lemma ofChildren_children (t : PreWFTree.{u} η) : ofChildren (children t) = t :=
--   sorry

noncomputable def children : (t : PreWFTree.{u} η) → Set (η × PreWFTree.{u} η)
  | ⟨_, f⟩ => Set.range f

instance small_children : ∀ (t : PreWFTree.{u} η), Small.{u} t.children
  | ⟨_, f⟩ => inferInstanceAs (Small.{u} (Set.range f))

instance : Inhabited (PreWFTree.{u} η) where
  default := ⟨PEmpty, fun.⟩

open Classical in
/-- Only well-defined if `Small.{u} ↥s`. -/
noncomputable def ofChildren (s : Set (η × PreWFTree.{u} η)) : PreWFTree.{u} η :=
  if _ : Small.{u} s then
    ⟨Shrink.{u} s, Subtype.val ∘ (equivShrink s).symm⟩
  else default

lemma ofChildren_def (s : Set (η × PreWFTree.{u} η)) [h : Small.{u} s] :
    ofChildren s = ⟨Shrink.{u} s, Subtype.val ∘ (equivShrink s).symm⟩ := by
  simp [ofChildren, h]

@[simp]
lemma children_mk (ι : Type u) (f : ι → η × PreWFTree η) :
    children ⟨ι, f⟩ = Set.range f := rfl

@[simp]
lemma children_ofChildren (s : Set (η × PreWFTree.{u} η)) [Small.{u} s] :
    children (ofChildren s) = s := by
  simp [ofChildren_def, children_mk]

def IsChildOf (t₁ t₂ : PreWFTree.{u} η) : Prop :=
  ∃ e, (e, t₁) ∈ t₂.children

instance : WellFoundedRelation (PreWFTree.{u} η) where
  rel := IsChildOf
  wf := by
    constructor
    intro t
    apply PreWFTree.recOn (motive_1 := Acc IsChildOf) (motive_2 := fun (_, c) ↦ Acc IsChildOf c)
    · intro ι f ih
      constructor
      intro c ⟨e, hc⟩
      simp at hc
      rcases hc with ⟨i, hfi⟩
      specialize ih i
      rw [hfi] at ih
      exact ih
    · intro _ c ih
      exact ih

def Equiv (t₁ t₂ : PreWFTree.{u} η) : Prop :=
  Relator.BiTotal fun (⟨⟨e₁, c₁⟩, h₁⟩ : t₁.children) (⟨⟨e₂, c₂⟩, _⟩ : t₂.children) ↦
    have : c₁.IsChildOf t₁ := ⟨e₁, h₁⟩
    e₁ = e₂ ∧ Equiv c₁ c₂
termination_by t₁

-- theorem equiv_iff (t₁ t₂ : PreWFTree.{u} η) :
--     Equiv t₁ t₂ ↔ ∀ e, Relator.BiTotal
--       fun (⟨c₁, _⟩ : t₁.children e)
--         (⟨c₂, _⟩ : t₂.children e) ↦ Equiv c₁ c₂ := by
--   rw [Equiv]

theorem equiv_iff' (t₁ t₂ : PreWFTree.{u} η) :
    Equiv t₁ t₂ ↔ ∀ e c,
      (⟨e, c⟩ ∈ t₁.children → ∃ c₂, ⟨e, c₂⟩ ∈ t₂.children ∧ Equiv c c₂) ∧
      (⟨e, c⟩ ∈ t₂.children → ∃ c₁, ⟨e, c₁⟩ ∈ t₁.children ∧ Equiv c₁ c) := by
  rw [Equiv]
  simp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal, forall_and]

@[refl]
protected theorem Equiv.refl (t : PreWFTree.{u} η) : Equiv t t := by
  rw [equiv_iff']
  intro e c
  constructor
  <;> exact fun hc ↦ ⟨c, hc, have : c.IsChildOf t := ⟨e, hc⟩; Equiv.refl c⟩
termination_by t

protected theorem Equiv.euc {x y z : PreWFTree.{u} η} : Equiv x y → Equiv z y → Equiv x z := by
  rw [equiv_iff' x y, equiv_iff' z y, equiv_iff' x z]
  intro hxy hzy e c
  specialize hxy e
  specialize hzy e
  constructor
  · peel (hxy c).left with hcx h -- TODO: add destructuring to `peel`
    rcases h with ⟨cy, hcy, hcxy⟩
    peel (hzy cy).right hcy with cz hcz hcxz
    have : c.IsChildOf x := ⟨e, hcx⟩
    exact Equiv.euc hcxy hcxz
  · peel (hzy c).left with hcz h
    rcases h with ⟨cy, hcy, hczy⟩
    peel (hxy cy).right hcy with cx hcx hcxy
    have : cx.IsChildOf x := ⟨e, hcx⟩
    exact Equiv.euc hcxy hczy
termination_by x

@[symm]
protected theorem Equiv.symm {x y : PreWFTree.{u} η} : Equiv x y → Equiv y x :=
  (Equiv.refl y).euc

protected theorem Equiv.comm {x y : PreWFTree.{u} η} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩

@[trans]
protected theorem Equiv.trans {x y z : PreWFTree.{u} η} (h1 : Equiv x y) (h2 : Equiv y z) :
    Equiv x z :=
  h1.euc h2.symm

instance setoid : Setoid (PreWFTree.{u} η) :=
  ⟨Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

theorem equiv_iff {x y : PreWFTree.{u} η} :
    x ≈ y ↔ ∀ e c,
      (∃ c₁, ⟨e, c₁⟩ ∈ x.children ∧ c₁ ≈ c) ↔ -- TODO: investigate commuting ∧
      (∃ c₂, ⟨e, c₂⟩ ∈ y.children ∧ c₂ ≈ c) := by
  change Equiv x y ↔ ∀ e c, (∃ c₁, _ ∧ Equiv c₁ c) ↔ (∃ c₂, _ ∧ Equiv c₂ c)
  rw [equiv_iff']
  apply forall_congr'
  intro e
  constructor
  · intro h z
    constructor
    · intro ⟨cx, hcx, hcxz⟩
      have ⟨cy, hcy, hcxy⟩ := (h cx).left hcx
      use cy, hcy, hcxy.symm.euc hcxz.symm
    · intro ⟨cy, hcy, hcyz⟩
      have ⟨cx, hcx, hcxy⟩ := (h cy).right hcy
      use cx, hcx, Equiv.trans hcxy hcyz
  · intro h c
    constructor
    · intro hcx
      conv => congr; ext; rw [Equiv.comm]
      rw [← h]
      use c, hcx, Equiv.refl c
    · intro hcy
      rw [h]
      use c, hcy, Equiv.refl c

theorem exists_of_equiv {e : η} {x y c : PreWFTree.{u} η} (h : x ≈ y) (hc : (e, c) ∈ x.children) :
    ∃ c', (e, c') ∈ y.children ∧ c' ≈ c := by
  rw [equiv_iff] at h
  rw [← h]
  use c

noncomputable def depth (t : PreWFTree.{u} η) : Ordinal.{u} :=
  Ordinal.lsub.{u, u} fun x : Shrink.{u} t.children ↦ -- TODO: define Ordinal.sLsub for `Small.{u}` sets
    let ⟨⟨e, c⟩, h⟩ := (equivShrink t.children).symm x
    have : c.IsChildOf t := ⟨e, h⟩
    depth c
termination_by t

theorem lt_depth_iff {t : PreWFTree.{u} η} {o : Ordinal.{u}} :
    o < depth t ↔ ∃ e c, (e, c) ∈ t.children ∧ o ≤ depth c := by
  rw [depth, Ordinal.lt_lsub_iff]
  dsimp
  constructor
  · intro ⟨x, h⟩
    set x' := (equivShrink t.children).symm x
    rcases x' with ⟨⟨e, c⟩, hc⟩
    use e, c
  · intro ⟨e, c, hc, h⟩
    refine ⟨equivShrink t.children ⟨(e, c), hc⟩, ?_⟩
    simpa

theorem depth_le_iff {t : PreWFTree.{u} η} {o : Ordinal.{u}} :
    depth t ≤ o ↔ ∀ e c, (e, c) ∈ t.children → depth c < o := by
  rw [depth, Ordinal.lsub_le_iff]
  constructor
  · intro h e c hc
    simpa using h (equivShrink t.children ⟨(e, c), hc⟩)
  · intro h x
    let ⟨⟨e, c⟩, hc⟩ := (equivShrink t.children).symm x
    simpa using h e c hc

protected theorem IsChildOf.depth {t₁ t₂ : PreWFTree.{u} η} (h : t₁.IsChildOf t₂) :
    depth t₁ < depth t₂ := by
  rw [lt_depth_iff]
  rcases h with ⟨e, ht₁⟩
  use e, t₁

theorem depth_le_of_equiv {x y : PreWFTree.{u} η} (h : x ≈ y) : depth x ≤ depth y := by
  rw [depth_le_iff]
  intro e cx hcx
  have ⟨cy, hcy, hcxy⟩ := exists_of_equiv h hcx
  have hcy' : cy.IsChildOf y := ⟨e, hcy⟩
  calc depth cx ≤ depth cy := depth_le_of_equiv hcxy.symm
  _ < depth y := hcy'.depth
termination_by y

theorem depth_eq_of_equiv {t₁ t₂ : PreWFTree.{u} η} (h : t₁ ≈ t₂) : depth t₁ = depth t₂ :=
  le_antisymm (depth_le_of_equiv h) (depth_le_of_equiv h.symm)

theorem wellFounded_depth : WellFounded ((· < ·) on depth.{u} (η := η)) :=
  WellFounded.onFun Ordinal.lt_wf

-- inductive Equiv' : PreWFTree.{u} η → PreWFTree.{u} η → Prop where
-- | intro {t t'} (f : (e : η) → (t e).1 → (t' e).1) (g : (e : η) → (t' e).1 → (t e).1)
--   (hf : ∀ e, ∀ i₁, Equiv' ((t e).2 i₁) ((t' e).2 (f e i₁)))
--   (hg : ∀ e, ∀ i₂, Equiv' ((t e).2 (g e i₂)) ((t' e).2 i₂)) : Equiv' ⟨t⟩ ⟨t'⟩

end PreWFTree

/-- `WFTree.{u} η` is the type of well-founded trees with edges labelled by `η`
  and children as `u`-small sets. -/
def WFTree (η : Type v) : Type (max (u + 1) v) :=
  Quotient (PreWFTree.setoid.{u} (η := η)) -- TODO: avoid quotient defeq abuse?

namespace WFTree

variable {η : Type v}

#check Prod.map

noncomputable def children (t : WFTree.{u} η) : Set (η × WFTree.{u} η) :=
  Quotient.liftOn t (fun t ↦ {(e, c) | ∃ c', (e, c') ∈ t.children ∧ ⟦c'⟧ = c}) fun x y h ↦ by
    ext ez
    rcases ez with ⟨e, z⟩
    induction' z using Quotient.ind with z
    simpa [Set.mem_setOf_eq, Quotient.eq] using PreWFTree.equiv_iff.mp h e z

@[simp]
lemma _root_.exists_eq_right_left {α : Sort*} {p q : α → Prop} {a' : α} :
    (∃ a, p a ∧ a = a' ∧ q a) ↔ p a' ∧ q a' := by aesop
  -- constructor
  -- · rintro ⟨a, hp, rfl, hq⟩
  --   exact ⟨hp, hq⟩
  -- · rintro ⟨hp, hq⟩
  --   use a', hp, rfl, hq

instance small_children (t : WFTree.{u} η) : Small.{u} t.children := by
  induction' t using Quotient.ind with t
  convert small_image (fun (e, c) ↦ (e, (⟦c⟧ : WFTree.{u} η))) t.children
  ext ec
  rcases ec with ⟨e, c⟩
  simp_rw [children, Quotient.lift_mk, Set.mem_setOf_eq, Set.mem_image, Prod.exists, Prod.mk.injEq]
  rw [exists_comm]
  simp

noncomputable def ofChildren (s : Set (η × WFTree.{u} η)) : WFTree.{u} η :=
  ⟦PreWFTree.ofChildren ((fun (e, c) ↦ (e, Quotient.out c)) '' s)⟧

@[simp]
lemma children_ofChildren (s : Set (η × WFTree.{u} η)) [Small.{u} s] :
    children (ofChildren s) = s := by
  ext c
  rcases c with ⟨e, c⟩
  simp [children, ofChildren, Quotient.mk'_eq_mk]
  aesop

@[ext]
lemma ext {t₁ t₂ : WFTree.{u} η} (h : t₁.children = t₂.children) : t₁ = t₂ := by
  induction' t₁ using Quotient.ind with t₁
  induction' t₂ using Quotient.ind with t₂
  apply Quotient.sound
  rw [PreWFTree.equiv_iff]
  rw [Set.ext_iff, Prod.forall] at h
  peel h with e h
  erw [Quotient.forall] at h
  simpa [children] using h

@[simp]
lemma ofChildren_children (t : WFTree.{u} η) : ofChildren (children t) = t := by
  ext
  simp

noncomputable def ofChildren_equiv :
    { s : Set (η × WFTree.{u} η) // Small.{u} s} ≃ WFTree.{u} η where
  toFun := fun ⟨f, _⟩ ↦ ofChildren f
  invFun t := ⟨t.children, inferInstance⟩
  left_inv := fun ⟨f, hf⟩ ↦ by simp
  right_inv t := by simp

noncomputable def depth (t : WFTree.{u} η) : Ordinal.{u} :=
  Quotient.liftOn t PreWFTree.depth fun _ _ ↦ PreWFTree.depth_eq_of_equiv

-- def IsChildOf (t₁ t₂ : WFTree.{u} η) : Prop :=
--   ∃ e, (e, t₁) ∈ t₂.children

-- lemma isChildOf_iff {t₁ t₂ : WFTree.{u} η} : t₁.IsChildOf t₂ ↔ ∃ e, (e, t₁) ∈ t₂.children :=
--   Iff.rfl

@[local simp]
private lemma mem_children_mk {e : η} {x : WFTree.{u} η} {y : PreWFTree.{u} η} :
    (e, x) ∈ WFTree.children ⟦y⟧ ↔ ∃ c, ⟦c⟧ = x ∧ (e, c) ∈ y.children := by
  induction' x using Quotient.ind with x
  simp [children, PreWFTree.children]
  aesop

-- @[local simp]
-- private lemma mk_isChildOf_mk {t₁ t₂ : PreWFTree.{u} η} :
--     WFTree.IsChildOf ⟦t₁⟧ ⟦t₂⟧ ↔ ∃ c₁, c₁ ≈ t₁ ∧ c₁.IsChildOf t₂ := by
--   simp [IsChildOf, children, PreWFTree.IsChildOf]
--   aesop

end WFTree
