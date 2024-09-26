/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!

# The equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

A monad "is just" a monoid in the category of endofunctors.

# Definitions/Theorems

1. `toMon` associates a monoid object in `C ⥤ C` to any monad on `C`.
2. `monadToMon` is the functorial version of `toMon`.
3. `ofMon` associates a monad on `C` to any monoid object in `C ⥤ C`.
4. `monadMonEquiv` is the equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

-/


namespace CategoryTheory

open Category Mon_Class IsMon_Hom

universe v u -- morphism levels before object levels. See note [category_theory universes].

variable {C : Type u} [Category.{v} C]

namespace Monad

attribute [local instance] endofunctorMonoidalCategory

@[simps]
instance {M : Monad C} : Mon_Class (M : C ⥤ C) where
  one := M.η
  mul := M.μ
  mul_assoc := by ext; simp [M.assoc]

/-- To every `Monad C` we associated a monoid object in `C ⥤ C`. -/
@[simps!]
def toMon (M : Monad C) : Mon_ (C ⥤ C) where
  X := (M : C ⥤ C)

variable (C)

/-- Passing from `Monad C` to `Mon_ (C ⥤ C)` is functorial. -/
@[simps]
def monadToMon : Monad C ⥤ Mon_ (C ⥤ C) where
  obj := toMon
  map f := { hom := f.toNatTrans, isMon_Hom := {} }

variable {C}

/-- To every monoid object in `C ⥤ C` we associate a `Monad C`. -/
@[simps «η» «μ»]
def ofMon (M : Mon_ (C ⥤ C)) : Monad C where
  toFunctor := M.X
  «η» := η
  «μ» := μ
  left_unit := fun X => by
    -- Porting note: now using `erw`
    erw [← whiskerLeft_app, ← NatTrans.comp_app, Mon_Class.mul_one]
    rfl
  right_unit := fun X => by
    -- Porting note: now using `erw`
    erw [← whiskerRight_app, ← NatTrans.comp_app, Mon_Class.one_mul]
    rfl
  assoc := fun X => by
    rw [← whiskerLeft_app, ← whiskerRight_app, ← NatTrans.comp_app]
    -- Porting note: had to add this step:
    erw [Mon_Class.mul_assoc]
    simp

-- Porting note: `@[simps]` fails to generate `ofMon_obj`:
@[simp] lemma ofMon_obj (M : Mon_ (C ⥤ C)) (X : C) : (ofMon M).obj X = M.X.obj X := rfl

variable (C)

/-- Passing from `Mon_ (C ⥤ C)` to `Monad C` is functorial. -/
@[simps]
def monToMonad : Mon_ (C ⥤ C) ⥤ Monad C where
  obj := ofMon
  map {X Y} f :=
    { f.hom with
      app_η := by
        intro X
        erw [← NatTrans.comp_app, one_hom]
        simp only [Functor.id_obj, ofMon_obj, ofMon_η]
      app_μ := by
        intro Z
        erw [← NatTrans.comp_app, mul_hom]
        dsimp
        simp only [Category.assoc, NatTrans.naturality, ofMon_obj, ofMon] }

/-- Oh, monads are just monoids in the category of endofunctors (equivalence of categories). -/
@[simps]
def monadMonEquiv : Monad C ≌ Mon_ (C ⥤ C) where
  functor := monadToMon _
  inverse := monToMonad _
  unitIso :=
  { hom := { app := fun _ => { app := fun _ => 𝟙 _ } }
    inv := { app := fun _ => { app := fun _ => 𝟙 _ } } }
  counitIso :=
  { hom := { app := fun _ => { hom := 𝟙 _ } }
    inv := { app := fun _ => { hom := 𝟙 _ } } }

-- Sanity check
example (A : Monad C) {X : C} : ((monadMonEquiv C).unitIso.app A).hom.app X = 𝟙 _ :=
  rfl

end Monad

end CategoryTheory
