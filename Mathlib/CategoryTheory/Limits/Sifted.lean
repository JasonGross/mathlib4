/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
/-!
# Sifted categories

A category `C` is sifted if `C` is nonempty and the diagonal functor `C ⥤ C × C` is final.
Sifted categories can be caracterized as those such that the colimit functor `(C ⥤ Type) ⥤ Type `
preserves finite products. We achieve this characterization in this file.

## Main results
- `isSifted_of_hasBinaryCoproducts_and_nonempty`: A nonempty category with binary coproducts is
  sifted.
- `IsSifted.colimPreservesFiniteProductsOfIsSifted`: The `Type`-valued colimit functor for sifted
  diagrams preserves finite products.
- `IsSifted.of_colimit_preservesFiniteProducts`: The converse: if the `Type`-valued colimit functor
  preserves finite producs, the category is sifted.
- `IsSifted.of_final_functor_from_sifted`: A category admitting a final functor from a sifted
  category is itself sifted.

## References
- [nLab, *Sifted category*](https://ncatlab.org/nlab/show/sifted+category)
- [*Algebraic Theories*, Chapter 2.][Adámek_Rosický_Vitale_2010]
-/

universe w v v₁ u u₁

namespace CategoryTheory

open Limits Functor

section

variable (C : Type u) [Category.{v} C]

/-- A category `C` `IsSiftedOrEmpty` if the diagonal functor `C ⥤ C × C` is final. -/
abbrev IsSiftedOrEmpty : Prop := Final (diag C)

/-- A category `C` `IsSfited` if
1. the diagonal functor `C ⥤ C × C` is final.
2. there exists some object. -/
class IsSifted extends IsSiftedOrEmpty C : Prop where
  [nonempty : Nonempty C]

attribute [instance] IsSifted.nonempty

namespace IsSifted

variable {C}

/-- Being sifted is preserved by equivalences of categories -/
lemma isSifted_of_equiv [IsSifted C] {D : Type u₁} [Category.{v₁} D] (e : D ≌ C) : IsSifted D :=
  letI : Final (diag D) := by
    letI : D × D ≌ C × C:= Equivalence.prod e e
    have sq : (e.inverse ⋙ diag D ⋙ this.functor ≅ diag C) :=
        NatIso.ofComponents (fun c ↦ by dsimp [this]
                                        exact Iso.prod (e.counitIso.app c) (e.counitIso.app c))
    apply_rules [final_iff_comp_equivalence _ this.functor|>.mpr,
      final_iff_final_comp e.inverse _ |>.mpr, final_of_natIso sq.symm]
  letI : _root_.Nonempty D := ⟨e.inverse.obj (_root_.Nonempty.some IsSifted.nonempty)⟩
  ⟨⟩

/-- In particular a category is sifted iff and only if it is so when viewed as a small category -/
lemma isSifted_iff_asSmallIsSifted : IsSifted C ↔ IsSifted (AsSmall.{w} C) where
  mp _ := isSifted_of_equiv AsSmall.equiv.symm
  mpr _ := isSifted_of_equiv AsSmall.equiv

/-- A sifted category is connected. -/
instance [IsSifted C] : IsConnected C :=
  isConnected_of_zigzag
    (by intro c₁ c₂
        have X : StructuredArrow (c₁, c₂) (diag C) :=
          letI S : Final (diag C) := by infer_instance
          Nonempty.some (S.out (c₁, c₂)).is_nonempty
        use [X.right, c₂]
        constructor
        · constructor
          · exact Zag.of_hom X.hom.fst
          · simp
            exact Zag.of_inv X.hom.snd
        · rfl)

/-- A category with binary coproducts is sifted or empty. -/
instance [HasBinaryCoproducts C] : IsSiftedOrEmpty C := by
    constructor
    rintro ⟨c₁, c₂⟩
    haveI : _root_.Nonempty <| StructuredArrow (c₁,c₂) (diag C) :=
      ⟨.mk ((coprod.inl : c₁ ⟶ c₁ ⨿ c₂), (coprod.inr : c₂ ⟶ c₁ ⨿ c₂))⟩
    apply isConnected_of_zigzag
    rintro ⟨_, c, f⟩ ⟨_, c', g⟩
    dsimp only [const_obj_obj, diag_obj, prod_Hom] at f g
    use [.mk ((coprod.inl : c₁ ⟶ c₁ ⨿ c₂), (coprod.inr : c₂ ⟶ c₁ ⨿ c₂)), .mk (g.fst, g.snd)]
    simp only [colimit.cocone_x, diag_obj, Prod.mk.eta, List.chain_cons, List.Chain.nil, and_true,
      ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self,
      List.getLast_singleton]
    exact ⟨⟨Zag.of_inv <| StructuredArrow.homMk <| coprod.desc f.fst f.snd,
      Zag.of_hom <| StructuredArrow.homMk <| coprod.desc g.fst g.snd⟩, rfl⟩

/-- A nonempty category with binary coproducts is sifted. -/
instance isSifted_of_hasBinaryCoproducts_and_nonempty [_root_.Nonempty C] [HasBinaryCoproducts C] :
    IsSifted C where

end IsSifted

end

noncomputable section SmallCategory

open MonoidalCategory ChosenFiniteProducts

namespace IsSifted

variable {C : Type u} [SmallCategory.{u} C]

/-- We introducte an auxiliary external product on presheaves for convenience. -/
@[simps!]
private def externalProductFunctor : ((C ⥤ Type u) × (C ⥤ Type u) ⥤ C × C ⥤ Type u) :=
  prodFunctor ⋙ (whiskeringRight _ _ _).obj (tensor _)

private abbrev externalProduct (X Y : (C ⥤ Type u)) : (C × C ⥤ Type u) :=
  externalProductFunctor.obj <| Prod.mk X Y

local infixr:80 " ⊠ " => externalProduct

section

variable (X Y : C ⥤ Type u)
/-- An auxiliary isomorphisms that computes the colimit of a functor `C × C ⥤ Type`
that decomposes as an external product of two functors `C ⥤ Type` -/
private def colimBoxIsoColimTensColim : colimit (X ⊠ Y) ≅ (colimit X) ⊗ (colimit Y) :=
  calc colimit (X ⊠ Y)
    _ ≅ colimit <| (curry.obj _) ⋙ colim := colimitIsoColimitCurryCompColim _
    _ ≅ colimit <| _ ⋙ colim := HasColimit.isoOfNatIso <| isoWhiskerRight
        (NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ β_ _ _)) :
          curry.obj (X ⊠ Y) ≅ (X ⋙ const C) ⋙ tensorLeft Y)
        colim
    _ ≅ colimit <| colimit <| _ := preservesColimitIso colim _ |>.symm
    _ ≅ colimit <| (tensorLeft Y).obj <| colimit <| _ := HasColimit.isoOfNatIso
      (preservesColimitIso _ _).symm
    _ ≅ colimit <| (_ ⋙ tensorLeft Y).obj _ := HasColimit.isoOfNatIso <|
      (tensorLeft Y).mapIso (preservesColimitIso _ _).symm
    _ ≅ colimit <| Y ⋙ tensorLeft _ := HasColimit.isoOfNatIso <| NatIso.ofComponents
      (fun _ ↦ β_ _ _)
    _ ≅ (tensorLeft _).obj _ := preservesColimitIso (tensorLeft _) _ |>.symm

/-- Through the isomorphisms `colimBoxIsoColimTensColim` and `diagCompExternalProduct`,
the comparison map `colimit.pre (diag C)` is identified with the product comparison map for the
colimit functor. --/
private lemma factorization_prod_comparison_colim :
    letI diagCompExternalProduct : X ⊗ Y ≅ diag C ⋙ X ⊠ Y := NatIso.ofComponents
      (fun c ↦ Iso.refl _)
    (HasColimit.isoOfNatIso diagCompExternalProduct).hom ≫ colimit.pre _ _ ≫
      (colimBoxIsoColimTensColim X Y).hom = ChosenFiniteProducts.prodComparison colim X Y := by
  apply colimit.hom_ext; intro c
  -- First, we "bubble down" the maps to the colimits as much as we can
  dsimp [colimBoxIsoColimTensColim]
  simp only [Category.assoc, HasColimit.isoOfNatIso_ι_hom_assoc, Monoidal.tensorObj_obj, comp_obj,
    diag_obj, externalProductFunctor_obj_obj, NatIso.ofComponents_hom_app, Iso.refl_hom,
    colimit.ι_pre_assoc, Category.id_comp]
  erw [colimitIsoColimitCurryCompColim_ι_hom_assoc]
  simp only [externalProductFunctor_obj_obj, HasColimit.isoOfNatIso_ι_hom_assoc, comp_obj,
    colim_obj, tensorLeft_obj, isoWhiskerRight_hom, whiskerRight_app, NatIso.ofComponents_hom_app,
    colim_map, ι_preservesColimitsIso_inv_assoc, ι_colimMap_assoc, curry_obj_obj_obj,
    Monoidal.tensorObj_obj, const_obj_obj, Iso.symm_hom, mapIso_inv, tensorLeft_map,
    Monoidal.whiskerLeft_app, ι_preservesColimitsIso_inv,
    BraidedCategory.braiding_naturality_right_assoc]
  slice_lhs 2 3 => rw [← NatTrans.vcomp_app, NatTrans.vcomp_eq_comp, ι_preservesColimitsIso_inv]
  simp only [comp_obj, tensorRight_map, Monoidal.whiskerRight_app, ← comp_whiskerRight,
    const_obj_obj, Category.assoc]
  rw [← whisker_exchange, ← tensorHom_def']
  simp only [tensorLeft_map, Monoidal.whiskerLeft_app, const_obj_obj,
    BraidedCategory.braiding_naturality_right_assoc, SymmetricCategory.symmetry_assoc]
  -- Then we compose with the projections from the product.
  apply ChosenFiniteProducts.hom_ext
  · simp only [Category.assoc, ChosenFiniteProducts.tensorHom_fst,
    ChosenFiniteProducts.whiskerRight_fst_assoc]
    slice_rhs 2 3 => arg 2; change ChosenFiniteProducts.fst (colim.obj _) (colim.obj _)
    rw [ChosenFiniteProducts.prodComparison_fst]
    simp only [colim_map, ι_colimMap, Monoidal.tensorObj_obj]
    congr
    rw [← NatTrans.vcomp_app, NatTrans.vcomp_eq_comp, ι_preservesColimitsIso_inv]
    rfl
  · simp only [Category.assoc, ChosenFiniteProducts.tensorHom_snd,
    ChosenFiniteProducts.whiskerRight_snd_assoc]
    slice_rhs 2 3 => arg 2; change ChosenFiniteProducts.snd (colim.obj _) (colim.obj _)
    rw [ChosenFiniteProducts.prodComparison_snd]
    simp only [colim_map, ι_colimMap, Monoidal.tensorObj_obj]
    congr

variable [IsSifted C]

/-- If `C` is sifted, the canonical product comparison map for the `colim` functor
`(C ⥤ Type) ⥤ Type` is an isomorphism. -/
instance : IsIso (ChosenFiniteProducts.prodComparison colim X Y) := by
  rw [← factorization_prod_comparison_colim]
  iterate apply IsIso.comp_isIso' <;> infer_instance

instance colimPreservesLimitsOfPairsOfIsSifted {X Y : C ⥤ Type u}:
    PreservesLimit (pair X Y) colim := preservesLimitPairOfIsIsoProdComparison _ _ _

/-- Sifted colimits commute with binary products -/
instance colimPreservesBinaryProductsOfIsSifted :
    PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ _) ⥤ Type u) := by
  constructor
  intro F
  apply preservesLimitOfIsoDiagram colim (diagramIsoPair F).symm

/-- If `C` is sifted, the `colimit` functor `(C ⥤ Type) ⥤ Type` preserves terminal objects -/
instance colimPreservesTerminalObjectOfIsSifted :
    PreservesLimit (Functor.empty (C ⥤ Type u)) colim := by
  apply preservesTerminalOfIso
  symm
  apply (_ : ⊤_ (Type u) ≅ PUnit.{u +1}).trans
  · apply_rules [(Types.colimitConstPUnitIsoPUnit C).symm.trans, HasColimit.isoOfNatIso,
      IsTerminal.uniqueUpToIso _ terminalIsTerminal, evaluationJointlyReflectsLimits]
    intro k
    exact isLimitChangeEmptyCone _ Types.isTerminalPunit _ <| Iso.refl _
  · exact Types.isTerminalEquivIsoPUnit (⊤_ (Type u))|>.toFun terminalIsTerminal

instance colimPreservesLimitsOfShapePEmtyOfIsSifted :
    PreservesLimitsOfShape (Discrete PEmpty) (colim : (C ⥤ _) ⥤ Type u) :=
  preservesLimitsOfShapePemptyOfPreservesTerminal _

/-- Putting everything together, if `C` is sifted, the `colim` functor `(C ⥤ Type) ⥤ Type`
preserves finite products. -/
instance colimPreservesFiniteProductsOfIsSifted {J : Type*} [Fintype J] :
    PreservesLimitsOfShape (Discrete J) (colim : (C ⥤ _) ⥤ Type u ) :=
  preservesFiniteProductsOfPreservesBinaryAndTerminal _ J

end

section

open Opposite in
/-- If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves binary products, then `C` is sifted or
empty. -/
theorem isSiftedOrEmpty_of_colimit_preservesBinaryProducts
    [PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ _) ⥤ Type u)] :
    IsSiftedOrEmpty C := by
  apply cofinal_of_colimit_comp_coyoneda_iso_pUnit
  rintro ⟨c₁, c₂⟩
  calc colimit <| diag C ⋙ coyoneda.obj (op (c₁, c₂))
    _ ≅ colimit <| _ ⋙ (coyoneda.obj _) ⊠ (coyoneda.obj _) := HasColimit.isoOfNatIso <|
      isoWhiskerLeft _ <| NatIso.ofComponents (fun _ ↦ Iso.refl _)
    _ ≅ colimit (_ ⊗ _) := HasColimit.isoOfNatIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _)).symm
    _ ≅ (colimit _) ⊗ (colimit _) := ChosenFiniteProducts.prodComparisonIso colim _ _
    _ ≅ PUnit ⊗ PUnit := (Coyoneda.colimitCoyonedaIso _) ⊗ (Coyoneda.colimitCoyonedaIso _)
    _ ≅ PUnit := λ_ _

lemma isSiftedOrEmpty_of_colimit_preservesFiniteProducts
    [h : ∀ (n : ℕ), PreservesLimitsOfShape (Discrete (Fin n)) (colim : (C ⥤ _) ⥤ Type u)] :
    IsSiftedOrEmpty C := by
  rcases Finite.exists_equiv_fin WalkingPair with ⟨_, ⟨e⟩⟩
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) (colim : (C ⥤ _) ⥤ Type u) :=
    preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) _
  exact @isSiftedOrEmpty_of_colimit_preservesBinaryProducts _ _ this

lemma nonempty_of_colimit_preservesLimitsOfShapeFinZero
    [PreservesLimitsOfShape (Discrete (Fin 0)) (colim : (C ⥤ _) ⥤ Type u)] :
    _root_.Nonempty C := by
  suffices connected : IsConnected C by infer_instance
  rw [Types.isConnected_iff_colimit_constPUnitFunctor_iso_pUnit]
  constructor
  haveI : PreservesLimitsOfShape (Discrete PEmpty) (colim : (C ⥤ _) ⥤ Type u) :=
    preservesLimitsOfShapeOfEquiv (Discrete.equivalence finZeroEquiv') _
  apply HasColimit.isoOfNatIso (_: Types.constPUnitFunctor C ≅ (⊤_ (C ⥤ Type u))) |>.trans
  · apply PreservesTerminal.iso colim |>.trans
    exact Types.terminalIso
  · apply_rules [IsTerminal.uniqueUpToIso _ terminalIsTerminal, evaluationJointlyReflectsLimits]
    intro _
    exact isLimitChangeEmptyCone _ Types.isTerminalPunit _ <| Iso.refl _

/-- If the `colim` functor `(C ⥤ Type) ⥤ Type` preserves finite products, then `C` is sifted. -/
theorem of_colimit_preservesFiniteProducts
    [h : ∀ (n : ℕ), PreservesLimitsOfShape (Discrete (Fin n)) (colim : (C ⥤ _) ⥤ Type u)] :
  IsSifted C := by
  haveI _ := @isSiftedOrEmpty_of_colimit_preservesFiniteProducts _ _ h
  haveI := @nonempty_of_colimit_preservesLimitsOfShapeFinZero _ _ (h 0)
  constructor

attribute [local instance] of_colimit_preservesFiniteProducts in
/-- A filtered category is sifted. -/
lemma of_isFiltered [IsFiltered C] : IsSifted C := by
  infer_instance

/-- Auxiliary version of `IsSiftedOfFinalFunctorFromSifted` where everything is a small category. -/
theorem of_final_functor_from_sifted'
    {D : Type u} [SmallCategory.{u} D] [IsSifted C] (F : C ⥤ D) [Final F] : IsSifted D := by
  refine @of_colimit_preservesFiniteProducts _ _ ?_
  intro n
  constructor
  intro K
  have colim_comp_iso : (whiskeringLeft _ _ _).obj F ⋙ (colim : (C ⥤ _) ⥤ _) ≅
      (colim : (D ⥤ _) ⥤ Type u) :=
    NatIso.ofComponents
      (fun c ↦ Final.colimitIso F _)
      (by intro x y f
          dsimp [colimMap, Final.colimitIso]
          apply colimit.hom_ext
          intro t
          simp only [comp_obj, colimit.ι_pre_assoc]
          erw [IsColimit.ι_map]
          erw [IsColimit.ι_map_assoc]
          simp)
  apply preservesLimitOfNatIso K colim_comp_iso

end

end IsSifted

end SmallCategory

variable {C : Type u} [Category.{v} C]

/-- A functor admitting a final functor from a sifted category is sifted -/
theorem IsSifted.of_final_functor_from_sifted {D : Type u₁} [Category.{v₁} D] [IsSifted C]
    (F : C ⥤ D) [Final F] : IsSifted D := by
  rw [isSifted_iff_asSmallIsSifted.{max u v}]
  rename_i C_sifted F_final
  rw [isSifted_iff_asSmallIsSifted.{max u₁ v₁}] at C_sifted
  letI : (AsSmall.{max u₁ v₁} C) ⥤ (AsSmall.{max u v} D) :=
    AsSmall.equiv.inverse ⋙ F ⋙ AsSmall.equiv.functor
  have is_final : Final this := by infer_instance
  apply of_final_functor_from_sifted' this

end CategoryTheory
