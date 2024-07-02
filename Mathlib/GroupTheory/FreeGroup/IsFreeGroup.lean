/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Eric Wieser, Joachim Breitner
-/
import Mathlib.GroupTheory.FreeGroup.Basic

#align_import group_theory.is_free_group from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Free groups structures on arbitrary types

This file defines the notion of free basis of a group, which induces an isomorphism between the
group and the free group generated by the basis.

It also introduced a type class for groups which are free groups, i.e., for which some free basis
exists.

For the explicit construction of free groups, see `GroupTheory/FreeGroup`.

## Main definitions

* `FreeGroupBasis ι G` : a function from `ι` to `G` such that `G` is free over its image.
  Equivalently, an isomorphism between `G` and `FreeGroup ι`.

* `IsFreeGroup G` : a typeclass to indicate that `G` is free over some generators
* `Generators G` : given a group satisfying `IsFreeGroup G`, some indexing type over
  which `G` is free.
* `IsFreeGroup.of` : the canonical injection of `G`'s generators into `G`
* `IsFreeGroup.lift` : the universal property of the free group

## Main results

* `FreeGroupBasis.isFreeGroup`: a group admitting a free group basis is free.
* `IsFreeGroup.toFreeGroup`: any free group with generators `A` is equivalent to `FreeGroup A`.
* `IsFreeGroup.unique_lift`: the universal property of a free group.
* `FreeGroupBasis.ofUniqueLift`: a group satisfying the universal property of a free group admits
 a free group basis.

-/


universe u

open Function Set

noncomputable section

/-- A free group basis `FreeGroupBasis ι G` is a structure recording the isomorphism between a
group `G` and the free group over `ι`. One may think of such a basis as a function from `ι` to `G`
(which is registered through a `FunLike` instance) together with the fact that the morphism induced
by this function from `FreeGroup ι` to `G` is an isomorphism. -/
structure FreeGroupBasis (ι : Type*) (G : Type*) [Group G] where
  /-- `FreeGroupBasis.ofRepr` constructs a basis given an equivalence with a free group. -/
  ofRepr ::
    /-- `repr` is the isomorphism between the group `G` and the free group generated by `ι`. -/
    repr : G ≃* FreeGroup ι

/-- A group is free if it admits a free group basis. In the definition, we require the basis to
be in the same universe as `G`, although this property follows from the existence of a basis in
any universe, see `FreeGroupBasis.isFreeGroup`. -/
class IsFreeGroup (G : Type u) [Group G] : Prop where
  nonempty_basis : ∃ (ι : Type u), Nonempty (FreeGroupBasis ι G)

namespace FreeGroupBasis

variable {ι ι' G H : Type*} [Group G] [Group H]

/-- A free group basis for `G` over `ι` is associated to a map `ι → G` recording the images of
the generators. -/
instance instFunLike : FunLike (FreeGroupBasis ι G) ι G where
  coe b := fun i ↦ b.repr.symm (FreeGroup.of i)
  coe_injective' := by
    rintro ⟨b⟩  ⟨b'⟩ hbb'
    have H : (b.symm : FreeGroup ι →* G) = (b'.symm : FreeGroup ι →* G) := by
      ext i; exact congr_fun hbb' i
    have : b.symm = b'.symm := by ext x; exact DFunLike.congr_fun H x
    rw [ofRepr.injEq, ← MulEquiv.symm_symm b, ← MulEquiv.symm_symm b', this]

@[simp] lemma repr_apply_coe (b : FreeGroupBasis ι G) (i : ι) : b.repr (b i) = FreeGroup.of i := by
  change b.repr (b.repr.symm (FreeGroup.of i)) = FreeGroup.of i
  simp

/-- The canonical basis of the free group over `X`. -/
def ofFreeGroup (X : Type*) : FreeGroupBasis X (FreeGroup X) := ofRepr (MulEquiv.refl _)

@[simp] lemma ofFreeGroup_apply {X : Type*} (x : X) :
    FreeGroupBasis.ofFreeGroup X x = FreeGroup.of x :=
  rfl

/-- Reindex a free group basis through a bijection of the indexing sets. -/
protected def reindex (b : FreeGroupBasis ι G) (e : ι ≃ ι') : FreeGroupBasis ι' G :=
  ofRepr (b.repr.trans (FreeGroup.freeGroupCongr e))

@[simp] lemma reindex_apply (b : FreeGroupBasis ι G) (e : ι ≃ ι') (x : ι') :
    b.reindex e x = b (e.symm x) := rfl

/-- Pushing a free group basis through a group isomorphism. -/
protected def map (b : FreeGroupBasis ι G) (e : G ≃* H) : FreeGroupBasis ι H :=
  ofRepr (e.symm.trans b.repr)

@[simp] lemma map_apply (b : FreeGroupBasis ι G) (e : G ≃* H) (x : ι) :
    b.map e x = e (b x) := rfl

protected lemma injective (b : FreeGroupBasis ι G) : Injective b :=
  b.repr.symm.injective.comp FreeGroup.of_injective

/-- A group admitting a free group basis is a free group. -/
lemma isFreeGroup (b : FreeGroupBasis ι G) : IsFreeGroup G :=
  ⟨range b, ⟨b.reindex (Equiv.ofInjective (↑b) b.injective)⟩⟩

instance (X : Type*) : IsFreeGroup (FreeGroup X) :=
  (ofFreeGroup X).isFreeGroup

/-- Given a free group basis of `G` over `ι`, there is a canonical bijection between maps from `ι`
to a group `H` and morphisms from `G` to `H`. -/
@[simps!]
def lift (b : FreeGroupBasis ι G) : (ι → H) ≃ (G →* H) :=
  FreeGroup.lift.trans
    { toFun := fun f => f.comp b.repr.toMonoidHom
      invFun := fun f => f.comp b.repr.symm.toMonoidHom
      left_inv := fun f => by
        ext
        simp
      right_inv := fun f => by
        ext
        simp }

/-- If two morphisms on `G` coincide on the elements of a basis, then they coincide. -/
lemma ext_hom (b : FreeGroupBasis ι G) (f g : G →* H) (h : ∀ i, f (b i) = g (b i)) : f = g :=
  b.lift.symm.injective <| funext h

/-- If a group satisfies the universal property of a free group with respect to a given type, then
it admits a free group basis based on this type. Here, the universal property is expressed as
in `IsFreeGroup.lift` and its properties. -/
def ofLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (lift : ∀ {H : Type u} [Group H], (X → H) ≃ (G →* H))
    (lift_of : ∀ {H : Type u} [Group H], ∀ (f : X → H) (a), lift f (of a) = f a) :
    FreeGroupBasis X G where
  repr := MulEquiv.symm <| MonoidHom.toMulEquiv (FreeGroup.lift of) (lift FreeGroup.of)
      (by
        apply FreeGroup.ext_hom; intro x
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, FreeGroup.lift.of,
          lift_of])
      (by
        let lift_symm_of : ∀ {H : Type u} [Group H], ∀ (f : G →* H) (a), lift.symm f a = f (of a) :=
          by intro H _ f a; simp [← lift_of (lift.symm f)]
        apply lift.symm.injective; ext x
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, FreeGroup.lift.of,
          lift_of, lift_symm_of])

/-- If a group satisfies the universal property of a free group with respect to a given type, then
it admits a free group basis based on this type. Here
the universal property is expressed as in `IsFreeGroup.unique_lift`.  -/
def ofUniqueLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (h : ∀ {H : Type u} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a) :
    FreeGroupBasis X G :=
  let lift {H : Type u} [Group H] : (X → H) ≃ (G →* H) :=
    { toFun := fun f => Classical.choose (h f)
      invFun := fun F => F ∘ of
      left_inv := fun f => funext (Classical.choose_spec (h f)).left
      right_inv := fun F => ((Classical.choose_spec (h (F ∘ of))).right F fun _ => rfl).symm }
  let lift_of {H : Type u} [Group H] (f : X → H) (a : X) : lift f (of a) = f a :=
    congr_fun (lift.symm_apply_apply f) a
  ofLift X of @lift @lift_of

end FreeGroupBasis

namespace IsFreeGroup

variable (G : Type*) [Group G] [IsFreeGroup G]

/-- A set of generators of a free group, chosen arbitrarily -/
def Generators : Type _ := (IsFreeGroup.nonempty_basis (G := G)).choose

/-- Any free group is isomorphic to "the" free group. -/
irreducible_def mulEquiv : FreeGroup (Generators G) ≃* G :=
  (IsFreeGroup.nonempty_basis (G := G)).choose_spec.some.repr.symm

/-- A free group basis of a free group `G`, over the set `Generators G`. -/
def basis : FreeGroupBasis (Generators G) G := FreeGroupBasis.ofRepr (mulEquiv G).symm

/-- Any free group is isomorphic to "the" free group. -/
@[simps!]
def toFreeGroup : G ≃* FreeGroup (Generators G) :=
  (mulEquiv G).symm
#align is_free_group.to_free_group IsFreeGroup.toFreeGroup
#align is_free_group.to_free_group_apply IsFreeGroup.toFreeGroup_apply
#align is_free_group.to_free_group_symm_apply IsFreeGroup.toFreeGroup_symm_apply

variable {G}

/-- The canonical injection of G's generators into G -/
def of : Generators G → G :=
  (mulEquiv G).toFun ∘ FreeGroup.of
#align is_free_group.of IsFreeGroup.of

variable {H : Type*} [Group H]

/-- The equivalence between functions on the generators and group homomorphisms from a free group
given by those generators. -/
def lift : (Generators G → H) ≃ (G →* H) :=
  (basis G).lift
#align is_free_group.lift IsFreeGroup.lift

@[simp]
theorem lift_of (f : Generators G → H) (a : Generators G) : lift f (of a) = f a :=
  congr_fun (lift.symm_apply_apply f) a
#align is_free_group.lift_of IsFreeGroup.lift_of

@[simp]
theorem lift_symm_apply (f : G →* H) (a : Generators G) : (lift.symm f) a = f (of a) :=
  rfl
#align is_free_group.lift_symm_apply IsFreeGroup.lift_symm_apply

/- Do not register this as an ext lemma, as `Generators G` is not canonical. -/
theorem ext_hom ⦃f g : G →* H⦄ (h : ∀ a : Generators G, f (of a) = g (of a)) : f = g :=
  lift.symm.injective (funext h)
#align is_free_group.ext_hom IsFreeGroup.ext_hom

/-- The universal property of a free group: A function from the generators of `G` to another
group extends in a unique way to a homomorphism from `G`.

Note that since `IsFreeGroup.lift` is expressed as a bijection, it already
expresses the universal property.  -/
theorem unique_lift (f : Generators G → H) : ∃! F : G →* H, ∀ a, F (of a) = f a := by
  simpa only [Function.funext_iff] using lift.symm.bijective.existsUnique f
#align is_free_group.unique_lift IsFreeGroup.unique_lift

/-- If a group satisfies the universal property of a free group with respect to a given type, then
it is free. Here, the universal property is expressed as in `IsFreeGroup.lift` and its
properties. -/
lemma ofLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (lift : ∀ {H : Type u} [Group H], (X → H) ≃ (G →* H))
    (lift_of : ∀ {H : Type u} [Group H], ∀ (f : X → H) (a), lift f (of a) = f a) :
    IsFreeGroup G :=
  (FreeGroupBasis.ofLift X of lift lift_of).isFreeGroup

/-- If a group satisfies the universal property of a free group with respect to a given type, then
it is free. Here the universal property is expressed as in `IsFreeGroup.unique_lift`.  -/
lemma ofUniqueLift {G : Type u} [Group G] (X : Type u) (of : X → G)
    (h : ∀ {H : Type u} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a) :
    IsFreeGroup G :=
  (FreeGroupBasis.ofUniqueLift X of h).isFreeGroup

lemma ofMulEquiv (e : G ≃* H) : IsFreeGroup H :=
  ((basis G).map e).isFreeGroup

end IsFreeGroup

end
