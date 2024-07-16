/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Normalization of morphisms in monoidal categories
This file provides a tactic that normalizes morphisms in monoidal categories. This is used in the
string diagram widget given in `Mathlib.Tactic.StringDiagram`.
We say that the morphism `η` in a monoidal category is in normal form if
1. `η` is of the form `α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₘ ≫ ηₘ ≫ αₘ₊₁` where each `αᵢ` is a
  structural 2-morphism (consisting of associators and unitors),
2. each `ηᵢ` is a non-structural 2-morphism of the form `f₁ ◁ ... ◁ fₘ ◁ θ`, and
3. `θ` is of the form `ι ▷ g₁ ▷ ... ▷ gₗ`

Note that the structural morphisms `αᵢ` are not necessarily normalized, as the main purpose
is to get a list of the non-structural morphisms out.

Currently, the primary application of the normalization tactic in mind is drawing string diagrams,
which are graphical representations of morphisms in monoidal categories, in the infoview. When
drawing string diagrams, we often ignore associators and unitors (i.e., drawing morphisms in
strict monoidal categories). On the other hand, in Lean, it is considered difficult to formalize
the concept of strict monoidal categories due to the feature of dependent type theory. The
normalization tactic can remove associators and unitors from the expression, extracting the
necessary data for drawing string diagrams.

The current plan on drawing string diagrams (#10581) is to use
Penrose (https://github.com/penrose) via ProofWidget. However, it should be noted that the
normalization procedure in this file does not rely on specific settings, allowing for broader
application.

Future plans include the following. At least I (Yuma) would like to work on these in the future,
but it might not be immediate. If anyone is interested, I would be happy to discuss.

- Currently (#10581), the string diagrams only do drawing. It would be better they also generate
  proofs. That is, by manipulating the string diagrams displayed in the infoview with a mouse to
  generate proofs. In #10581, the string diagram widget only uses the morphisms generated by the
  normalization tactic and does not use proof terms ensuring that the original morphism and the
  normalized morphism are equal. Proof terms will be necessary for proof generation.

- There is also the possibility of using homotopy.io (https://github.com/homotopy-io), a graphical
  proof assistant for category theory, from Lean. At this point, I have very few ideas regarding
  this approach.

- The normalization tactic allows for an alternative implementation of the coherent tactic.

## Main definitions
- `Tactic.Monoidal.eval`: Given a Lean expression `e` that represents a morphism in a monoidal
category, this function returns a pair of `⟨e', pf⟩` where `e'` is the normalized expression of `e`
and `pf` is a proof that `e = e'`.

## Implementation notes
The function `Tactic.Monoidal.eval` fails to produce a proof term when the environment cannot
find the necessary `MonoidalCategory C` instance. This occurs when running the string diagram
widget, and the error makes it impossible for the string diagram widget to generate the diagram.
To work around the widget failure, if the proof generation fails when `eval` running, it returns a
meaningless term `mkConst ``True` in place of the proof term.
-/

namespace Mathlib.Tactic.Monoidal

open Lean Meta Elab
open CategoryTheory
open Mathlib.Tactic.Coherence

/-- The context for evaluating expressions. -/
structure Context where
  /-- The expression for the underlying category. -/
  C : Expr

/-- Populate a `context` object for evaluating `e`. -/
def mkContext (e : Expr) : MetaM Context := do
  match (← inferType e).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) =>
    let C ← inferType f
    return ⟨C⟩
  | _ => throwError "not a morphism"

/-- The monad for the normalization of 2-morphisms. -/
abbrev MonoidalM := ReaderT Context MetaM

/-- Run a computation in the `M` monad. -/
abbrev MonoidalM.run {α : Type} (c : Context) (m : MonoidalM α) : MetaM α :=
  ReaderT.run m c

/-- Expressions for atomic 1-morphisms. -/
structure Atom₁ : Type where
  /-- Extract a Lean expression from an `Atom₁` expression. -/
  e : Expr

/-- Expressions for 1-morphisms. -/
inductive Mor₁ : Type
  /-- `id` is the expression for `𝟙_ C`. -/
  | id : Mor₁
  /-- `comp X Y` is the expression for `X ⊗ Y` -/
  | comp : Mor₁ → Mor₁ → Mor₁
  /-- Construct the expression for an atomic 1-morphism. -/
  | of : Atom₁ → Mor₁
  deriving Inhabited

/-- Converts a 1-morphism into a list of its components. -/
def Mor₁.toList : Mor₁ → List Atom₁
  | .id => []
  | .comp f g => f.toList ++ g.toList
  | .of f => [f]

/-- Returns `𝟙_ C` if the expression `e` is of the form `𝟙_ C`. -/
def isTensorUnit? (e : Expr) : MetaM (Option Expr) := do
  let C ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let unit := mkAppN (← mkConstWithFreshMVarLevels
    ``MonoidalCategoryStruct.tensorUnit) #[C, instC, instMC]
  if ← withDefault <| isDefEq e unit then
    return ← instantiateMVars unit
  else
    return none

/-- Returns `(f, g)` if the expression `e` is of the form `f ⊗ g`. -/
def isTensorObj? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let C ← mkFreshExprMVar none
  let f ← mkFreshExprMVar C
  let g ← mkFreshExprMVar C
  let instC ← mkFreshExprMVar none
  let instMC ← mkFreshExprMVar none
  let fg := mkAppN (← mkConstWithFreshMVarLevels
    ``MonoidalCategoryStruct.tensorObj) #[C, instC, instMC, f, g]
  if ← withDefault <| isDefEq e fg then
    return (← instantiateMVars f, ← instantiateMVars g)
  else
    return none

/-- Construct a `Mor₁` expression from a Lean expression. -/
partial def toMor₁ (e : Expr) : MetaM Mor₁ := do
  if let some _ ← isTensorUnit? e then
    return Mor₁.id
  else if let some (f, g) ← isTensorObj? e then
    return (← toMor₁ f).comp (← toMor₁ g)
  else
    return Mor₁.of ⟨e⟩

/-- Expressions for atomic structural 2-morphisms. -/
inductive StructuralAtom : Type
  /-- The expression for the associator `(α_ f g h).hom`. -/
  | associator (f g h : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the associator `(α_ f g h).inv`. -/
  | associatorInv (f g h : Mor₁) : StructuralAtom
  /-- The expression for the left unitor `(λ_ f).hom`. -/
  | leftUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the left unitor `(λ_ f).inv`. -/
  | leftUnitorInv (f : Mor₁) : StructuralAtom
  /-- The expression for the right unitor `(ρ_ f).hom`. -/
  | rightUnitor (f : Mor₁) : StructuralAtom
  /-- The expression for the inverse of the right unitor `(ρ_ f).inv`. -/
  | rightUnitorInv (f : Mor₁) : StructuralAtom
  deriving Inhabited

/-- Construct a `StructuralAtom` expression from a Lean expression. -/
def structuralAtom? (e : Expr) : MetaM (Option StructuralAtom) := do
  match e.getAppFnArgs with
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associator (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      return some <| .leftUnitor (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      return some <| .rightUnitor (← toMor₁ f)
    | _ => return none
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``MonoidalCategoryStruct.associator, #[_, _, _, f, g, h]) =>
      return some <| .associatorInv (← toMor₁ f) (← toMor₁ g) (← toMor₁ h)
    | (``MonoidalCategoryStruct.leftUnitor, #[_, _, _, f]) =>
      return some <| .leftUnitorInv (← toMor₁ f)
    | (``MonoidalCategoryStruct.rightUnitor, #[_, _, _, f]) =>
      return some <| .rightUnitorInv (← toMor₁ f)
    | _ => return none
  | _ => return none

/-- Expressions for atomic non-structural 2-morphisms. -/
structure Atom where
  /-- Extract a Lean expression from an `Atom` expression. -/
  e : Expr
  deriving Inhabited

/-- Expressions of the form `η ▷ f₁ ▷ ... ▷ fₙ`. -/
inductive WhiskerRightExpr : Type
  /-- Construct the expression for an atomic 2-morphism. -/
  | of (η : Atom) : WhiskerRightExpr
  /-- Construct the expression for `η ▷ f`. -/
  | whisker (η : WhiskerRightExpr) (f : Atom₁) : WhiskerRightExpr
  deriving Inhabited

/-- Expressions of the form `η₁ ⊗ ... ⊗ ηₙ`. -/
inductive TensorHomExpr : Type
  | of (η : WhiskerRightExpr) : TensorHomExpr
  | cons (head : WhiskerRightExpr) (tail : TensorHomExpr) : TensorHomExpr
  deriving Inhabited

/-- Expressions of the form `f₁ ◁ ... ◁ fₙ ◁ η`. -/
inductive WhiskerLeftExpr : Type
  /-- Construct the expression for a right-whiskered 2-morphism. -/
  | of (η : TensorHomExpr) : WhiskerLeftExpr
  /-- Construct the expression for `f ◁ η`. -/
  | whisker (f : Atom₁) (η : WhiskerLeftExpr) : WhiskerLeftExpr
  deriving Inhabited

/-- Expressions for structural 2-morphisms. -/
inductive Structural : Type
  /-- Expressions for atomic structural 2-morphisms. -/
  | atom (η : StructuralAtom) : Structural
  /-- Expressions for the identity `𝟙 f`. -/
  | id (f : Mor₁) : Structural
  /-- Expressions for the composition `η ≫ θ`. -/
  | comp (α β : Structural) : Structural
  /-- Expressions for the left whiskering `f ◁ η`. -/
  | whiskerLeft (f : Mor₁) (η : Structural) : Structural
  /-- Expressions for the right whiskering `η ▷ f`. -/
  | whiskerRight (η : Structural) (f : Mor₁) : Structural
  /-- Expressions for the tensor `α ⊗ β`. -/
  | tensorHom (α β : Structural) : Structural
  /-- Expressions for `α` in the monoidal composition `η ⊗≫ θ := η ≫ α ≫ θ`. -/
  | monoidalCoherence (f g : Mor₁) (e : Expr) : Structural
  deriving Inhabited

/-- Normalized expressions for 2-morphisms. -/
inductive NormalExpr : Type
  /-- Construct the expression for a structural 2-morphism. -/
  | nil (α : Structural) : NormalExpr
  /-- Construct the normalized expression of 2-morphisms recursively. -/
  | cons (head_structural : Structural) (head : WhiskerLeftExpr) (tail : NormalExpr) : NormalExpr
  deriving Inhabited

/-- The domain of a morphism. -/
def src (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, f, _]) => toMor₁ f
  | _ => throwError "{η} is not a morphism"

/-- The codomain of a morphism. -/
def tgt (η : Expr) : MetaM Mor₁ := do
  match (← inferType η).getAppFnArgs with
  | (``Quiver.Hom, #[_, _, _, g]) => toMor₁ g
  | _ => throwError "{η} is not a morphism"

/-- The domain of a 2-morphism. -/
def Atom.src (η : Atom) : MetaM Mor₁ := do Monoidal.src η.e

/-- The codomain of a 2-morphism. -/
def Atom.tgt (η : Atom) : MetaM Mor₁ := do Monoidal.tgt η.e

/-- The domain of a 2-morphism. -/
def WhiskerRightExpr.src : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.src
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.src η).comp (Mor₁.of f)

/-- The codomain of a 2-morphism. -/
def WhiskerRightExpr.tgt : WhiskerRightExpr → MetaM Mor₁
  | WhiskerRightExpr.of η => η.tgt
  | WhiskerRightExpr.whisker η f => return (← WhiskerRightExpr.tgt η).comp (Mor₁.of f)

/-- The domain of a 2-morphism. -/
def TensorHomExpr.src : TensorHomExpr → MetaM Mor₁
  | TensorHomExpr.of η => η.src
  | TensorHomExpr.cons η ηs => return (← η.src).comp (← ηs.src)

/-- The codomain of a 2-morphism. -/
def TensorHomExpr.tgt : TensorHomExpr → MetaM Mor₁
  | TensorHomExpr.of η => η.tgt
  | TensorHomExpr.cons η ηs => return (← η.tgt).comp (← ηs.tgt)

/-- The domain of a 2-morphism. -/
def WhiskerLeftExpr.src : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => TensorHomExpr.src η
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← WhiskerLeftExpr.src η)

/-- The codomain of a 2-morphism. -/
def WhiskerLeftExpr.tgt : WhiskerLeftExpr → MetaM Mor₁
  | WhiskerLeftExpr.of η => TensorHomExpr.tgt η
  | WhiskerLeftExpr.whisker f η => return (Mor₁.of f).comp (← WhiskerLeftExpr.tgt η)

/-- The domain of a 2-morphism. -/
def StructuralAtom.src : StructuralAtom → Mor₁
  | .associator f g h => (f.comp g).comp h
  | .associatorInv f g h => f.comp (g.comp h)
  | .leftUnitor f => Mor₁.id.comp f
  | .leftUnitorInv f => f
  | .rightUnitor f => f.comp Mor₁.id
  | .rightUnitorInv f => f

/-- The codomain of a 2-morphism. -/
def StructuralAtom.tgt : StructuralAtom → Mor₁
  | .associator f g h => f.comp (g.comp h)
  | .associatorInv f g h => (f.comp g).comp h
  | .leftUnitor f => f
  | .leftUnitorInv f => Mor₁.id.comp f
  | .rightUnitor f => f
  | .rightUnitorInv f => f.comp Mor₁.id

/-- The domain of a 2-morphism. -/
def Structural.src : Structural → Mor₁
  | .atom η => η.src
  | .id f => f
  | .comp α _ => α.src
  | .whiskerLeft f η => f.comp η.src
  | .whiskerRight η f => η.src.comp f
  | .tensorHom α β => α.src.comp β.src
  | .monoidalCoherence f _ _ => f

/-- The codomain of a 2-morphism. -/
def Structural.tgt : Structural → Mor₁
  | .atom η => η.tgt
  | .id f => f
  | .comp _ β => β.tgt
  | .whiskerLeft f η => f.comp η.tgt
  | .whiskerRight η f => η.tgt.comp f
  | .tensorHom α β => α.tgt.comp β.tgt
  | .monoidalCoherence _ g _ => g

/-- The domain of a 2-morphism. -/
def NormalExpr.src : NormalExpr → Mor₁
  | NormalExpr.nil η => η.src
  | NormalExpr.cons α _ _ => α.src

/-- The codomain of a 2-morphism. -/
def NormalExpr.tgt : NormalExpr → Mor₁
  | NormalExpr.nil η => η.tgt
  | NormalExpr.cons _ _ ηs => ηs.tgt

/-- The associator as a term of `normalExpr`. -/
def NormalExpr.associator (f g h : Mor₁) : NormalExpr :=
  .nil <| .atom <| .associator f g h

/-- The inverse of the associator as a term of `normalExpr`. -/
def NormalExpr.associatorInv (f g h : Mor₁) : NormalExpr :=
  .nil <| .atom <| .associatorInv f g h

/-- The left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitor (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .leftUnitor f

/-- The inverse of the left unitor as a term of `normalExpr`. -/
def NormalExpr.leftUnitorInv (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .leftUnitorInv f

/-- The right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitor (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .rightUnitor f

/-- The inverse of the right unitor as a term of `normalExpr`. -/
def NormalExpr.rightUnitorInv (f : Mor₁) : NormalExpr :=
  .nil <| .atom <| .rightUnitorInv f

/-- Construct a `Structural` expression from a Lean expression for a structural 2-morphism. -/
partial def structural? (e : Expr) : MetaM Structural := do
  match (← whnfR e).getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, α, β]) =>
    return .comp (← structural? α) (← structural? β)
  | (``CategoryStruct.id, #[_, f]) => return .id (← toMor₁ f)
  | (``MonoidalCategoryStruct.whiskerLeft, #[f, η]) =>
    return .whiskerLeft (← toMor₁ f) (← structural? η)
  | (``MonoidalCategoryStruct.whiskerRight, #[η, f]) =>
    return .whiskerRight (← structural? η) (← toMor₁ f)
  | (``MonoidalCoherence.hom, #[_, _, f, g, inst]) =>
    return .monoidalCoherence (← toMor₁ f) (← toMor₁ g) inst
  | _ => match ← structuralAtom? e with
    | some η => return .atom η
    | none => throwError "not a structural 2-morphism"

/-- Construct a `NormalExpr` expression from a `WhiskerLeftExpr` expression. -/
def NormalExpr.of (η : WhiskerLeftExpr) : MetaM NormalExpr := do
  return .cons (.id (← η.src)) η (.nil (.id (← η.tgt)))

/-- Construct a `NormalExpr` expression from a Lean expression for an atomic 2-morphism. -/
def NormalExpr.ofExpr (η : Expr) : MetaM NormalExpr :=
  NormalExpr.of <| .of <| .of <| .of ⟨η⟩

/-- If `e` is an expression of the form `η ⊗≫ θ := η ≫ α ≫ θ` in the monoidal category `C`,
return the expression for `α` .-/
def structuralOfMonoidalComp (C e : Expr) : MetaM Structural := do
  let v ← mkFreshLevelMVar
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ v)) (← inferType (← inferType e))
  _ ← isDefEq (.sort (.succ u)) (← inferType C)
  let W ← mkFreshExprMVar none
  let X ← mkFreshExprMVar none
  let Y ← mkFreshExprMVar none
  let Z ← mkFreshExprMVar none
  let f ← mkFreshExprMVar none
  let g ← mkFreshExprMVar none
  let α₀ ← mkFreshExprMVar none
  let instC ← mkFreshExprMVar none
  let αg := mkAppN (.const ``CategoryStruct.comp [v, u]) #[C, instC, X, Y, Z, α₀, g]
  let fαg := mkAppN (.const ``CategoryStruct.comp [v, u]) #[C, instC, W, X, Z, f, αg]
  _ ← isDefEq e fαg
  structural? α₀

section

open scoped MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable {f f' g g' h h' i i' j : C}

@[nolint synTaut]
theorem ofNormalExpr_nil (α : f ⟶ g) (β : g ⟶ h) :
    α ≫ β = α ≫ β := by
  simp

theorem ofNormalExpr_cons (α : f ⟶ g) (β : g ⟶ h) (η : h ⟶ i) (ηs : i ⟶ j) :
    α ≫ (β ≫ η ≫ ηs) = (α ≫ β) ≫ η ≫ ηs := by
  simp

theorem evalComp_nil_cons {f g h i j : C} (α : f ⟶ g) (β : g ⟶ h) (η : h ⟶ i) (ηs : i ⟶ j) :
    α ≫ (β ≫ η ≫ ηs) = (α ≫ β) ≫ η ≫ ηs := by
  simp

@[nolint synTaut]
theorem evalComp_nil_nil {f g h : C} (α : f ⟶ g) (β : g ⟶ h) :
    α ≫ β = α ≫ β := by
  simp

theorem evalComp_cons {f g h i j : C} (α : f ⟶ g) (η : g ⟶ h) {ηs : h ⟶ i} {θ : i ⟶ j} {ι : h ⟶ j}
    (pf_ι : ηs ≫ θ = ι)  :
    (α ≫ η ≫ ηs) ≫ θ = α ≫ η ≫ ι := by
  simp [pf_ι]

@[nolint synTaut]
theorem evalWhiskerLeft_nil (f : C) (α : g ⟶ h) :
    f ◁ α = f ◁ α := by
  simp

theorem evalWhiskerLeft_of_cons
    (α : g ⟶ h) (η : h ⟶ i) {ηs : i ⟶ j} {θ : f ⊗ i ⟶ f ⊗ j} (pf_θ : f ◁ ηs = θ) :
    f ◁ (α ≫ η ≫ ηs) = f ◁ α ≫ f ◁ η ≫ θ := by
  simp [pf_θ]

theorem evalWhiskerLeft_comp {η : h ⟶ i} {θ : g ⊗ h ⟶ g ⊗ i} {ι : f ⊗ g ⊗ h ⟶ f ⊗ g ⊗ i}
    {ι' : f ⊗ g ⊗ h ⟶ (f ⊗ g) ⊗ i} {ι'' : (f ⊗ g) ⊗ h ⟶ (f ⊗ g) ⊗ i}
    (pf_θ : g ◁ η = θ) (pf_ι : f ◁ θ = ι)
    (pf_ι' : ι ≫ (α_ _ _ _).inv = ι') (pf_ι'' : (α_ _ _ _).hom ≫ ι' = ι'') :
    (f ⊗ g) ◁ η = ι'' := by
  simp [pf_θ, pf_ι, pf_ι', pf_ι'']

theorem evalWhiskerLeft_id {f g : C} {η : f ⟶ g}
    {η' : f ⟶ 𝟙_ C ⊗ g} {η'' : 𝟙_ C ⊗ f ⟶ 𝟙_ C ⊗ g}
    (pf_η' : η ≫ (λ_ _).inv = η') (pf_η'' : (λ_ _).hom ≫ η' = η'') :
    𝟙_ C ◁ η = η'' := by
  simp [pf_η', pf_η'']

theorem eval_comp
    {η η' : f ⟶ g} {θ θ' : g ⟶ h} {ι : f ⟶ h}
    (pf_η : η = η') (pf_θ : θ = θ') (pf_ηθ : η' ≫ θ' = ι) :
    η ≫ θ = ι := by
  simp [pf_η, pf_θ, pf_ηθ]

theorem eval_whiskerLeft
    {η η' : g ⟶ h} {θ : f ⊗ g ⟶ f ⊗ h}
    (pf_η : η = η') (pf_θ : f ◁ η' = θ) :
    f ◁ η = θ := by
  simp [pf_η, pf_θ]

theorem eval_whiskerRight
    {η η' : f ⟶ g} {θ : f ⊗ h ⟶ g ⊗ h}
    (pf_η : η = η') (pf_θ : η' ▷ h = θ) :
    η ▷ h = θ := by
  simp [pf_η, pf_θ]

theorem eval_tensorHom
    {η η' : f ⟶ g} {θ θ' : h ⟶ i} {ι : f ⊗ h ⟶ g ⊗ i}
    (pf_η : η = η') (pf_θ : θ = θ') (pf_ι : η' ⊗ θ' = ι) :
    η ⊗ θ = ι := by
  simp [pf_η, pf_θ, pf_ι]

theorem eval_of (η : f ⟶ g) :
    η = 𝟙 _ ≫ η ≫ 𝟙 _ := by
  simp

@[nolint synTaut]
theorem evalWhiskerRight_nil (α : f ⟶ g) (h : C) :
    α ▷ h = α ▷ h := by
  simp

theorem evalWhiskerRight_cons_of_of
    {α : f ⟶ g} {η : g ⟶ h} {ηs : h ⟶ i} {ηs₁ : h ⊗ j ⟶ i ⊗ j}
    {η₁ : g ⊗ j ⟶ h ⊗ j} {η₂ : g ⊗ j ⟶ i ⊗ j} {η₃ : f ⊗ j ⟶ i ⊗ j}
    (pf_ηs₁ : ηs ▷ j = ηs₁) (pf_η₁ : η ▷ j = η₁)
    (pf_η₂ : η₁ ≫ ηs₁ = η₂) (pf_η₃ : α ▷ j ≫ η₂ = η₃) :
    (α ≫ η ≫ ηs) ▷ j = η₃ := by
  simp_all

theorem evalWhiskerRight_cons_whisker
    {α : g ⟶ f ⊗ h} {η : h ⟶ i} {ηs : f ⊗ i ⟶ j} {k : C}
    {η₁ : h ⊗ k ⟶ i ⊗ k} {η₂ : f ⊗ (h ⊗ k) ⟶ f ⊗ (i ⊗ k)} {ηs₁ : (f ⊗ i) ⊗ k ⟶ j ⊗ k}
    {ηs₂ : f ⊗ (i ⊗ k) ⟶ j ⊗ k} {η₃ : f ⊗ (h ⊗ k) ⟶ j ⊗ k} {η₄ : (f ⊗ h) ⊗ k ⟶ j ⊗ k}
    {η₅ : g ⊗ k ⟶ j ⊗ k}
    (pf_η₁ : (𝟙 _ ≫ η ≫ 𝟙 _ ) ▷ k = η₁) (pf_η₂ : f ◁ η₁ = η₂)
    (pf_ηs₁ : ηs ▷ k = ηs₁) (pf_ηs₂ : (α_ _ _ _).inv ≫ ηs₁ = ηs₂)
    (pf_η₃ : η₂ ≫ ηs₂ = η₃) (pf_η₄ : (α_ _ _ _).hom ≫ η₃ = η₄) (pf_η₅ : α ▷ k ≫ η₄ = η₅) :
    (α ≫ (f ◁ η) ≫ ηs) ▷ k = η₅ := by
  simp at pf_η₁
  simp [pf_η₁, pf_η₂, pf_ηs₁, pf_ηs₂, pf_η₃, pf_η₄, pf_η₅]

theorem evalWhiskerRight_comp
    {η : f ⟶ f'} {η₁ : f ⊗ g ⟶ f' ⊗ g} {η₂ : (f ⊗ g) ⊗ h ⟶ (f' ⊗ g) ⊗ h}
    {η₃ : (f ⊗ g) ⊗ h ⟶ f' ⊗ (g ⊗ h)} {η₄ : f ⊗ (g ⊗ h) ⟶ f' ⊗ (g ⊗ h)}
    (pf_η₁ : η ▷ g = η₁) (pf_η₂ : η₁ ▷ h = η₂)
    (pf_η₃ : η₂ ≫ (α_ _ _ _).hom = η₃) (pf_η₄ : (α_ _ _ _).inv ≫ η₃ = η₄) :
    η ▷ (g ⊗ h) = η₄ := by
  simp [pf_η₁, pf_η₂, pf_η₃, pf_η₄]

theorem evalWhiskerRight_id
    {η : f ⟶ g} {η₁ : f ⟶ g ⊗ 𝟙_ C} {η₂ : f ⊗ 𝟙_ C ⟶ g ⊗ 𝟙_ C}
    (pf_η₁ : η ≫ (ρ_ _).inv = η₁) (pf_η₂ : (ρ_ _).hom ≫ η₁ = η₂) :
    η ▷ 𝟙_ C = η₂ := by
  simp [pf_η₁, pf_η₂]

theorem eval_monoidalComp
    {η η' : f ⟶ g} {α : g ⟶ h} {θ θ' : h ⟶ i} {αθ : g ⟶ i} {ηαθ : f ⟶ i}
    (pf_η : η = η') (pf_θ : θ = θ') (pf_αθ : α ≫ θ' = αθ) (pf_ηαθ : η' ≫ αθ = ηαθ) :
    η ≫ α ≫ θ = ηαθ := by
  simp [pf_η, pf_θ, pf_αθ, pf_ηαθ]

theorem evalWhiskerRightExprAux_of (η : g ⟶ h) (f : C) :
    η ▷ f = 𝟙 _ ≫ η ▷ f ≫ 𝟙 _ := by
  simp

theorem evalWhiskerRightExprAux_cons {η : g ⟶ h} {ηs : h ⟶ i}
    {ηs' : h ⊗ f ⟶ i ⊗ f} {η₁ : g ⊗ (h ⊗ f) ⟶ h ⊗ (i ⊗ f)}
    {η₂ : g ⊗ (h ⊗ f) ⟶ (h ⊗ i) ⊗ f} {η₃ : (g ⊗ h) ⊗ f ⟶ (h ⊗ i) ⊗ f}
    (pf_ηs' : ηs ▷ f = ηs') (pf_η₁ : (𝟙 _ ≫ η ≫ 𝟙 _) ⊗ ηs' = η₁)
    (pf_η₂ : η₁ ≫ (α_ _ _ _).inv = η₂) (pf_η₃ : (α_ _ _ _).hom ≫ η₂ = η₃) :
    (η ⊗ ηs) ▷ f = η₃ := by
  simp [← pf_ηs', ← pf_η₁, ← pf_η₂, ← pf_η₃, MonoidalCategory.tensorHom_def]

theorem evalWhiskerRightExpr_cons_of {α : f' ⟶ g} {η : g ⟶ h} {ηs : h ⟶ i}
    {ηs₁ : h ⊗ f ⟶ i ⊗ f} {η₁ : g ⊗ f ⟶ h ⊗ f} {η₂ : g ⊗ f ⟶ i ⊗ f}
    {η₃ : f' ⊗ f ⟶ i ⊗ f}
    (pf_ηs₁ : ηs ▷ f = ηs₁) (pf_η₁ : η ▷ f = η₁)
    (pf_η₂ : η₁ ≫ ηs₁ = η₂) (pf_η₃ : α ▷ f ≫ η₂ = η₃) :
    (α ≫ η ≫ ηs) ▷ f = η₃ := by
  simp [pf_ηs₁, pf_η₁, pf_η₂, pf_η₃]

theorem evalTensorHomAux_of (η : f ⟶ g) (θ : h ⟶ i) :
    η ⊗ θ = 𝟙 _ ≫ (η ⊗ θ) ≫ 𝟙 _ := by
  simp

theorem evalTensorHomAux_cons {η : f ⟶ g} {ηs : f' ⟶ g'} {θ : h ⟶ i}
    {ηθ : f' ⊗ h ⟶ g' ⊗ i} {η₁ : f ⊗ (f' ⊗ h) ⟶ g ⊗ (g' ⊗ i)}
    {ηθ₁ : f ⊗ (f' ⊗ h) ⟶ (g ⊗ g') ⊗ i} {ηθ₂ : (f ⊗ f') ⊗ h ⟶ (g ⊗ g') ⊗ i}
    (pf_ηθ : ηs ⊗ θ = ηθ) (pf_η₁ : η ⊗ ηθ = η₁)
    (pf_ηθ₁ : η₁ ≫ (α_ _ _ _).inv = ηθ₁) (pf_ηθ₂ : (α_ _ _ _).hom ≫ ηθ₁ = ηθ₂) :
    (η ⊗ ηs) ⊗ θ = ηθ₂ := by
  simp_all

theorem evalTensorHomAux'_whisker {η : g ⟶ h} {θ : f' ⟶ g'}
    {ηθ : g ⊗ f' ⟶ h ⊗ g'} {η₁ : f ⊗ (g ⊗ f') ⟶ f ⊗ (h ⊗ g')}
    {η₂ :  f ⊗ (g ⊗ f') ⟶ (f ⊗ h) ⊗ g'} {η₃ : (f ⊗ g) ⊗ f' ⟶ (f ⊗ h) ⊗ g'}
    (pf_ηθ : η ⊗ θ = ηθ) (pf_η₁ : f ◁ ηθ = η₁)
    (pf_η₂ : η₁ ≫ (α_ _ _ _).inv = η₂) (pf_η₃ : (α_ _ _ _).hom ≫ η₂ = η₃) :
    (f ◁ η) ⊗ θ = η₃ := by
  simp only [← pf_ηθ, ← pf_η₁, ← pf_η₂, ← pf_η₃]
  simp [MonoidalCategory.tensorHom_def]

theorem evalTensorHomAux'_of_whisker {η : g ⟶ h} {θ : f' ⟶ g'}
    {η₁ : g ⊗ f ⟶ h ⊗ f} {ηθ : (g ⊗ f) ⊗ f' ⟶ (h ⊗ f) ⊗ g'}
    {ηθ₁ : (g ⊗ f) ⊗ f' ⟶ h ⊗ (f ⊗ g')}
    {ηθ₂ : g ⊗ (f ⊗ f') ⟶ h ⊗ (f ⊗ g')}
    (pf_η₁ : η ▷ f = η₁) (pf_ηθ : η₁ ⊗ (𝟙 _ ≫ θ ≫ 𝟙 _) = ηθ)
    (pf_ηθ₁ : ηθ ≫ (α_ _ _ _).hom = ηθ₁) (pf_ηθ₂ : (α_ _ _ _).inv ≫ ηθ₁ = ηθ₂) :
    η ⊗ (f ◁ θ) = ηθ₂ := by
  simp only [← pf_η₁, ← pf_ηθ, ← pf_ηθ₁, ← pf_ηθ₂]
  simp [MonoidalCategory.tensorHom_def]

@[nolint synTaut]
theorem evalTensorHomExpr_nil_nil (α : f ⟶ g) (β : h ⟶ i) :
    α ⊗ β = α ⊗ β := by
  simp

theorem evalTensorHomExpr_nil_cons {α : f ⟶ g} {β : f' ⟶ g'} {η : g' ⟶ h} {ηs : h ⟶ i}
    {η₁ : g ⊗ g' ⟶ g ⊗ h} {ηs₁ : g ⊗ h ⟶ g ⊗ i}
    {η₂ : g ⊗ g' ⟶ g ⊗ i} {η₃ : f ⊗ f' ⟶ g ⊗ i}
    (pf_η₁ : g ◁ (𝟙 _ ≫ η ≫ 𝟙 _) = η₁)
    (pf_ηs₁ : g ◁ ηs = ηs₁) (pf_η₂ : η₁ ≫ ηs₁ = η₂)
    (pf_η₃ : (α ⊗ β) ≫ η₂ = η₃) :
    α ⊗ (β ≫ η ≫ ηs) = η₃ := by
  simp_all [MonoidalCategory.tensorHom_def]

theorem evalTensorHomExpr_cons_nil {α : f ⟶ g} {η : g ⟶ h} {ηs : h ⟶ i} {β : f' ⟶ g'}
    {η₁ : g ⊗ g' ⟶ h ⊗ g'} {ηs₁ : h ⊗ g' ⟶ i ⊗ g'} {η₂ : g ⊗ g' ⟶ i ⊗ g'} {η₃ : f ⊗ f' ⟶ i ⊗ g'}
    (pf_η₁ : (𝟙 _ ≫ η ≫ 𝟙 _) ▷ g' = η₁) (pf_ηs₁ : ηs ▷ g' = ηs₁)
    (pf_η₂ : η₁ ≫ ηs₁ = η₂) (pf_η₃ : (α ⊗ β) ≫ η₂ = η₃) :
    (α ≫ η ≫ ηs) ⊗ β = η₃ := by
  simp_all [MonoidalCategory.tensorHom_def']

theorem evalTensorHomExpr_cons_cons {α : f ⟶ g} {η : g ⟶ h} {ηs : h ⟶ i}
    {β : f' ⟶ g'} {θ : g' ⟶ h'} {θs : h' ⟶ i'}
    {ηθ : g ⊗ g' ⟶ h ⊗ h'} {ηθs : h ⊗ h' ⟶ i ⊗ i'}
    {ηθ₁ : g ⊗ g' ⟶ i ⊗ i'} {ηθ₂ : f ⊗ f' ⟶ i ⊗ i'}
    (pf_ηθ : η ⊗ θ = ηθ) (pf_ηθs : ηs ⊗ θs = ηθs)
    (pf_ηθ₁ : ηθ ≫ ηθs = ηθ₁) (pf_ηθ₂ : (α ⊗ β) ≫ ηθ₁ = ηθ₂) :
    (α ≫ η ≫ ηs) ⊗ (β ≫ θ ≫ θs) = ηθ₂ := by
  simp [← pf_ηθ , ← pf_ηθs , ← pf_ηθ₁, ← pf_ηθ₂]

end

/-- Extract a Lean expression from a `Mor₁` expression. -/
def Mor₁.e : Mor₁ → MonoidalM Expr
  | .id => do
    let ctx ← read
    mkAppOptM ``MonoidalCategoryStruct.tensorUnit #[ctx.C, none, none]
  | .comp f g => do
    mkAppM ``MonoidalCategoryStruct.tensorObj #[← Mor₁.e f, ← Mor₁.e g]
  | .of f => return f.e

/-- Extract a Lean expression from a `StructuralAtom` expression. -/
def StructuralAtom.e : StructuralAtom → MonoidalM Expr
  | .associator f g h => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .associatorInv f g h => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.associator #[← f.e, ← g.e, ← h.e]]
  | .leftUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .leftUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.leftUnitor #[← f.e]]
  | .rightUnitor f => do
    mkAppM ``Iso.hom #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]
  | .rightUnitorInv f => do
    mkAppM ``Iso.inv #[← mkAppM ``MonoidalCategoryStruct.rightUnitor #[← f.e]]

/-- Extract a Lean expression from a `Structural` expression. -/
partial def Structural.e : Structural → MonoidalM Expr
  | .atom η => η.e
  | .id f => do mkAppM ``CategoryStruct.id #[← f.e]
  | .comp α β => do mkAppM ``CategoryStruct.comp #[← α.e, ← β.e]
  | .whiskerLeft f η => do mkAppM ``MonoidalCategoryStruct.whiskerLeft #[← f.e, ← η.e]
  | .whiskerRight η f => do mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, ← f.e]
  | .tensorHom α β => do mkAppM ``MonoidalCategoryStruct.tensorHom #[← α.e, ← β.e]
  | .monoidalCoherence _ _ e => do
    mkAppOptM ``MonoidalCoherence.hom #[none, none, none, none, e]

/-- Extract a Lean expression from a `WhiskerRightExpr` expression. -/
def WhiskerRightExpr.e : WhiskerRightExpr → MonoidalM Expr
  | WhiskerRightExpr.of η => return η.e
  | WhiskerRightExpr.whisker η f => do
    mkAppM ``MonoidalCategoryStruct.whiskerRight #[← η.e, f.e]

/-- Extract a Lean expression from a `TensorHomExpr` expression. -/
def TensorHomExpr.e : TensorHomExpr → MonoidalM Expr
  | TensorHomExpr.of η => η.e
  | TensorHomExpr.cons η ηs => do
    mkAppM ``MonoidalCategoryStruct.tensorHom #[← η.e, ← ηs.e]

/-- Extract a Lean expression from a `WhiskerLeftExpr` expression. -/
def WhiskerLeftExpr.e : WhiskerLeftExpr → MonoidalM Expr
  | WhiskerLeftExpr.of η => η.e
  | WhiskerLeftExpr.whisker f η => do
    mkAppM ``MonoidalCategoryStruct.whiskerLeft #[f.e, ← η.e]

/-- Extract a Lean expression from a `NormalExpr` expression. -/
def NormalExpr.e : NormalExpr → MonoidalM Expr
  | NormalExpr.nil α => α.e
  | NormalExpr.cons α η θ => do
    mkAppM ``CategoryStruct.comp #[← α.e, ← mkAppM ``CategoryStruct.comp #[← η.e, ← θ.e]]

/-- The result of evaluating an expression into normal form. -/
structure Result where
  /-- The normalized expression of the 2-morphism. -/
  expr : NormalExpr
  /-- The proof that the normalized expression is equal to the original expression. -/
  proof : Expr

/-- Trying to construct a normalized expression, where the proof term is given by the lemma `nm`
with arguments `args`. When we work in the string diagram widget, the environment cannot find
the appropriate instance such as `MonoidalCategory C` and the application of the lemma fails.
In this case, we return the garbage proof term `mkConst ``True` instead of throwing an error
as it prevents the widget from displaying the diagram. -/
def tryNormalize (e : NormalExpr) (nm : Name) (args : Array Expr) : MetaM Result := do
  try return ⟨e, ← mkAppM nm args⟩
  catch _ =>
    return ⟨e, mkConst ``True⟩

/-- Construct a `NormalExpr` expression from another `NormalExpr` expression by adding a structural
2-morphism at the head. -/
def NormalExpr.ofNormalExpr (α : Structural) (e : NormalExpr) : MonoidalM Result :=
  match e with
  | .nil β => do
    let αβ := .nil (α.comp β)
    tryNormalize αβ ``ofNormalExpr_nil #[← α.e, ← β.e]
  | .cons β η ηs => do
    let αβ := .cons (α.comp β) η ηs
    tryNormalize αβ ``ofNormalExpr_cons #[← α.e, ← β.e, ← η.e, ← ηs.e]

mutual

/-- Evaluate the expression `η ≫ θ` into a normalized form. -/
partial def evalComp : NormalExpr → NormalExpr → MonoidalM Result
  | .nil α, .cons β η ηs => do
    let η' := .cons (α.comp β) η ηs
    tryNormalize η' ``evalComp_nil_cons #[← α.e, ← β.e, ← η.e, ← ηs.e]
  | .nil α, .nil α' => do
    tryNormalize (.nil (α.comp α')) ``evalComp_nil_nil #[← α.e, ← α'.e]
  | .cons α η ηs, θ => do
    let ⟨ι, pf_ι⟩ ← evalComp ηs θ
    let ι' := .cons α η ι
    tryNormalize ι' ``evalComp_cons #[← α.e, ← η.e, pf_ι]

/-- Evaluate the expression `f ◁ η` into a normalized form. -/
partial def evalWhiskerLeftExpr : Mor₁ → NormalExpr → MonoidalM Result
  | f, .nil α => do
    tryNormalize (.nil (.whiskerLeft f α)) ``evalWhiskerLeft_nil #[← f.e, ← α.e]
  | .of f, .cons α η ηs => do
    let η' := WhiskerLeftExpr.whisker f η
    let ⟨θ, pf_θ⟩ ← evalWhiskerLeftExpr (.of f) ηs
    let η'' := .cons (.whiskerLeft (.of f) α) η' θ
    tryNormalize η'' ``evalWhiskerLeft_of_cons #[← α.e, ← η.e, pf_θ]
  | .comp f g, η => do
    let ⟨θ, pf_θ⟩ ← evalWhiskerLeftExpr g η
    let ⟨ι, pf_ι⟩ ← evalWhiskerLeftExpr f θ
    let h := η.src
    let h' := η.tgt
    let ⟨ι', pf_ι'⟩ ← evalComp ι (NormalExpr.associatorInv f g h')
    let ⟨ι'', pf_ι''⟩ ← evalComp (NormalExpr.associator f g h) ι'
    tryNormalize ι'' ``evalWhiskerLeft_comp #[pf_θ, pf_ι, pf_ι', pf_ι'']
  | .id, η => do
    let f := η.src
    let g := η.tgt
    let ⟨η', pf_η'⟩ ← evalComp η (NormalExpr.leftUnitorInv g)
    let ⟨η'', pf_η''⟩ ← evalComp (NormalExpr.leftUnitor f) η'
    tryNormalize η'' ``evalWhiskerLeft_id #[pf_η', pf_η'']

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExprAux : TensorHomExpr → Atom₁ → MonoidalM Result
  | .of η, f => do
    let η' ← NormalExpr.of <| .of <| .of <| .whisker η f
    tryNormalize η' ``evalWhiskerRightExprAux_of #[← η.e, f.e]
  | .cons η ηs, f => do
    let ⟨ηs', pf_ηs'⟩ ← evalWhiskerRightExprAux ηs f
    let ⟨η₁, pf_η₁⟩ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηs'
    let ⟨η₂, pf_η₂⟩ ← evalComp η₁ (.associatorInv (← η.tgt) (← ηs.tgt) (.of f))
    let ⟨η₃, pf_η₃⟩ ← evalComp (.associator (← η.src) (← ηs.src) (.of f)) η₂
    tryNormalize η₃ ``evalWhiskerRightExprAux_cons #[pf_ηs', pf_η₁, pf_η₂, pf_η₃]

/-- Evaluate the expression `η ▷ f` into a normalized form. -/
partial def evalWhiskerRightExpr : NormalExpr → Mor₁ → MonoidalM Result
  | .nil α, h => do
    tryNormalize (.nil (.whiskerRight α h)) ``evalWhiskerRight_nil #[← α.e, ← h.e]
  | .cons α (.of η) ηs, .of f => do
    let ⟨ηs₁, pf_ηs₁⟩ ← evalWhiskerRightExpr ηs (.of f)
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExprAux η f
    let ⟨η₂, pf_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, pf_η₃⟩ ← NormalExpr.ofNormalExpr (.whiskerRight α (.of f)) η₂
    tryNormalize η₃ ``evalWhiskerRight_cons_of_of #[pf_ηs₁, pf_η₁, pf_η₂, pf_η₃]
  | .cons α (.whisker f η) ηs, h => do
    let g ← η.src
    let g' ← η.tgt
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExpr (.cons (.id g) η (.nil (.id g'))) h
    let ⟨η₂, pf_η₂⟩ ← evalWhiskerLeftExpr (.of f) η₁
    let ⟨ηs₁, pf_ηs₁⟩ ← evalWhiskerRightExpr ηs h
    let α' := .whiskerRight α h
    let ⟨ηs₂, pf_ηs₂⟩ ← evalComp (.associatorInv (.of f) g' h) ηs₁
    let ⟨η₃, pf_η₃⟩ ← evalComp η₂ ηs₂
    let ⟨η₄, pf_η₄⟩ ← evalComp (.associator (.of f) g h) η₃
    let ⟨η₅, pf_η₅⟩ ← evalComp (.nil α') η₄
    tryNormalize η₅
      ``evalWhiskerRight_cons_whisker #[pf_η₁, pf_η₂, pf_ηs₁, pf_ηs₂, pf_η₃, pf_η₄, pf_η₅]
  | η, .comp g h => do
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExpr η g
    let ⟨η₂, pf_η₂⟩ ← evalWhiskerRightExpr η₁ h
    let f := η.src
    let f' := η.tgt
    let ⟨η₃, pf_η₃⟩ ← evalComp η₂ (.associator f' g h)
    let ⟨η₄, pf_η₄⟩ ← evalComp (.associatorInv f g h) η₃
    tryNormalize η₄ ``evalWhiskerRight_comp #[pf_η₁, pf_η₂, pf_η₃, pf_η₄]
  | η, .id => do
    let f := η.src
    let g := η.tgt
    let ⟨η₁, pf_η₁⟩ ← evalComp η (.rightUnitorInv g)
    let ⟨η₂, pf_η₂⟩ ← evalComp (.rightUnitor f) η₁
    tryNormalize η₂ ``evalWhiskerRight_id #[pf_η₁, pf_η₂]

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomAux : TensorHomExpr → TensorHomExpr → MonoidalM Result
  | .of η, θ => do
    tryNormalize (← NormalExpr.of <| .of <| .cons η θ) ``evalTensorHomAux_of #[← η.e, ← θ.e]
  | .cons η ηs, θ => do
    let α := NormalExpr.associator (← η.src) (← ηs.src) (← θ.src)
    let α' := NormalExpr.associatorInv (← η.tgt) (← ηs.tgt) (← θ.tgt)
    let ⟨ηθ, pf_ηθ⟩ ← evalTensorHomAux ηs θ
    let ⟨η₁, pf_η₁⟩ ← evalTensorHomExpr (← NormalExpr.of <| .of <| .of η) ηθ
    let ⟨ηθ₁, pf_ηθ₁⟩ ← evalComp η₁ α'
    let ⟨ηθ₂, pf_ηθ₂⟩ ← evalComp α ηθ₁
    tryNormalize ηθ₂ ``evalTensorHomAux_cons #[pf_ηθ, pf_η₁, pf_ηθ₁, pf_ηθ₂]

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomAux' : WhiskerLeftExpr → WhiskerLeftExpr → MonoidalM Result
  | .of η, .of θ => evalTensorHomAux η θ
  | .whisker f η, θ => do
    let ⟨ηθ, pf_ηθ⟩ ← evalTensorHomAux' η θ
    let ⟨ηθ₁, pf_ηθ₁⟩ ← evalWhiskerLeftExpr (.of f) ηθ
    let ⟨ηθ₂, pf_ηθ₂⟩ ← evalComp ηθ₁ (.associatorInv (.of f) (← η.tgt) (← θ.tgt))
    let ⟨ηθ₃, pf_ηθ₃⟩ ← evalComp (.associator (.of f) (← η.src) (← θ.src)) ηθ₂
    tryNormalize ηθ₃ ``evalTensorHomAux'_whisker #[pf_ηθ, pf_ηθ₁, pf_ηθ₂, pf_ηθ₃]
  | .of η, .whisker f θ => do
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExprAux η f
    let ⟨ηθ, pf_ηθ⟩ ← evalTensorHomExpr η₁ (← NormalExpr.of θ)
    let ⟨ηθ₁, pf_ηθ₁⟩ ← evalComp ηθ (.associator (← η.tgt) (.of f) (← θ.tgt))
    let ⟨ηθ₂, pf_ηθ₂⟩ ← evalComp (.associatorInv (← η.src) (.of f) (← θ.src)) ηθ₁
    tryNormalize ηθ₂ ``evalTensorHomAux'_of_whisker #[pf_η₁, pf_ηθ, pf_ηθ₁, pf_ηθ₂]

/-- Evaluate the expression `η ⊗ θ` into a normalized form. -/
partial def evalTensorHomExpr : NormalExpr → NormalExpr → MonoidalM Result
  | .nil α, .nil β => do
    tryNormalize (.nil <| .tensorHom α β) ``evalTensorHomExpr_nil_nil #[← α.e, ← β.e]
  | .nil α, .cons β η ηs => do
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerLeftExpr α.tgt (← NormalExpr.of η)
    let ⟨ηs₁, pf_ηs₁⟩ ← evalWhiskerLeftExpr α.tgt ηs
    let ⟨η₂, pf_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, pf_η₃⟩ ← NormalExpr.ofNormalExpr (α.tensorHom β) η₂
    tryNormalize η₃ ``evalTensorHomExpr_nil_cons #[pf_η₁, pf_ηs₁, pf_η₂, pf_η₃]
  | .cons α η ηs, .nil β => do
    let ⟨η₁, pf_η₁⟩ ← evalWhiskerRightExpr (← NormalExpr.of η) β.tgt
    let ⟨ηs₁, pf_ηs₁⟩ ← evalWhiskerRightExpr ηs β.tgt
    let ⟨η₂, pf_η₂⟩ ← evalComp η₁ ηs₁
    let ⟨η₃, pf_η₃⟩ ← NormalExpr.ofNormalExpr (α.tensorHom β) η₂
    tryNormalize η₃ ``evalTensorHomExpr_cons_nil #[pf_η₁, pf_ηs₁, pf_η₂, pf_η₃]
  | .cons α η ηs, .cons β θ θs => do
    let ⟨ηθ, pf_ηθ⟩ ← evalTensorHomAux' η θ
    let ⟨ηθs, pf_ηθs⟩ ← evalTensorHomExpr ηs θs
    let ⟨ηθ₁, pf_ηθ₁⟩ ← evalComp ηθ ηθs
    let ⟨ηθ₂, pf_ηθ₂⟩ ← NormalExpr.ofNormalExpr (α.tensorHom β) ηθ₁
    tryNormalize ηθ₂ ``evalTensorHomExpr_cons_cons #[pf_ηθ, pf_ηθs, pf_ηθ₁, pf_ηθ₂]

end

/-- Evaluate the expression of a 2-morphism into a normalized form. -/
partial def eval (e : Expr) : MonoidalM Result := do
  if let .some α ← structuralAtom? e then
    tryNormalize (.nil <| .atom α) ``Eq.refl #[← α.e]
  else
    match e.getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, f]) =>
      tryNormalize (.nil (.id (← toMor₁ f))) ``Eq.refl #[← mkAppM ``CategoryStruct.id #[f]]
    | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let ⟨θ_e, pf_θ⟩ ← eval θ
      let ⟨ηθ, pf⟩ ← evalComp η_e θ_e
      tryNormalize ηθ ``eval_comp #[pf_η, pf_θ, pf]
    | (``MonoidalCategoryStruct.whiskerLeft, #[_, _, _, f, _, _, η]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let ⟨θ, pf_θ⟩ ← evalWhiskerLeftExpr (← toMor₁ f) η_e
      tryNormalize θ ``eval_whiskerLeft #[pf_η, pf_θ]
    | (``MonoidalCategoryStruct.whiskerRight, #[_, _, _, _, _, η, h]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let ⟨θ, pf_θ⟩ ← evalWhiskerRightExpr η_e (← toMor₁ h)
      tryNormalize θ ``eval_whiskerRight #[pf_η, pf_θ]
    | (``monoidalComp, #[C, _, _, _, _, _, _, η, θ]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let α₀ ← structuralOfMonoidalComp C e
      let α := NormalExpr.nil α₀
      let ⟨θ_e, pf_θ⟩ ← eval θ
      let ⟨αθ, pf_θα⟩ ← evalComp α θ_e
      let ⟨ηαθ, pf_ηαθ⟩ ← evalComp η_e αθ
      tryNormalize ηαθ ``eval_monoidalComp #[pf_η, pf_θ, pf_θα, pf_ηαθ]
    | (``MonoidalCategoryStruct.tensorHom, #[_, _, _, _, _, _, _, η, θ]) =>
      let ⟨η_e, pf_η⟩ ← eval η
      let ⟨θ_e, pf_θ⟩ ← eval θ
      let ⟨ηθ, pf⟩ ← evalTensorHomExpr η_e θ_e
      tryNormalize ηθ ``eval_tensorHom #[pf_η, pf_θ, pf]
    | _ =>
      tryNormalize (← NormalExpr.ofExpr e) ``eval_of #[e]

/-- Convert a `NormalExpr` expression into a list of `WhiskerLeftExpr` expressions. -/
def NormalExpr.toList : NormalExpr → List WhiskerLeftExpr
  | NormalExpr.nil _ => []
  | NormalExpr.cons _ η ηs => η :: NormalExpr.toList ηs

end Mathlib.Tactic.Monoidal

open Mathlib.Tactic.Monoidal

/-- `normalize% η` is the normalization of the 2-morphism `η`.
1. The normalized 2-morphism is of the form `α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₘ ≫ ηₘ ≫ αₘ₊₁` where
  each `αᵢ` is a structural 2-morphism (consisting of associators and unitors),
2. each `ηᵢ` is a non-structural 2-morphism of the form `f₁ ◁ ... ◁ fₘ ◁ θ`, and
3. `θ` is of the form `ι ▷ g₁ ▷ ... ▷ gₗ`
-/
elab "normalize% " t:term:51 : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  MonoidalM.run (← mkContext e) do (← eval e).expr.e

theorem mk_eq {α : Type _} (a b a' b' : α) (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  simp [h, ha, hb]

open Lean Elab Meta Tactic in
/-- Transform an equality between 2-morphisms into the equality between their normalizations. -/
def mkEq (e : Expr) : MetaM Expr := do
  let some (_, e₁, e₂) := (← whnfR <| e).eq?
    | throwError "monoidal_nf requires an equality goal"
  MonoidalM.run (← mkContext e₁) do
    let ⟨e₁', p₁⟩ ← eval e₁
    let ⟨e₂', p₂⟩ ← eval e₂
    mkAppM ``mk_eq #[e₁, e₂, ← e₁'.e, ← e₂'.e, p₁, p₂]

open Lean Elab Tactic in
/-- Normalize the both sides of an equality. -/
elab "monoidal_nf" : tactic => withMainContext do
  let t ← getMainTarget
  let mvarIds ← (← getMainGoal).apply (← mkEq t)
  replaceMainGoal mvarIds
