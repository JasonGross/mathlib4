/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.ContinuousMap.Basic

open scoped Topology
open Filter

class ContinuousEvalConst (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
    [TopologicalSpace F] [TopologicalSpace Y] : Prop where
  continuous_eval_const (x : X) : Continuous fun f : F ↦ f x

export ContinuousEvalConst (continuous_eval_const)

section ContinuousEvalConst

variable {F X Y Z : Type*} [FunLike F X Y] [TopologicalSpace F] [TopologicalSpace Y]
  [ContinuousEvalConst F X Y] [TopologicalSpace Z] {f : Z → F} {s : Set Z} {z : Z}

-- TODO: docstring
theorem ContinuousEvalConst.of_continuous_forget {F' : Type*} [FunLike F' X Y] [TopologicalSpace F']
    {f : F' → F} (hc : Continuous f) (hf : ∀ g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEvalConst F' X Y where
  continuous_eval_const x := by simpa only [← hf] using (continuous_eval_const x).comp hc

@[continuity, fun_prop]
theorem Continuous.eval_const (hf : Continuous f) (x : X) : Continuous (f · x) :=
  (continuous_eval_const x).comp hf

theorem continuous_coeFun : Continuous (DFunLike.coe : F → X → Y) :=
  continuous_pi continuous_eval_const

protected theorem Continuous.coeFun (hf : Continuous f) : Continuous fun z ↦ ⇑(f z) :=
  continuous_pi hf.eval_const

theorem Filter.Tendsto.eval_const {α : Type*} {l : Filter α} {f : α → F} {g : F}
    (hf : Tendsto f l (𝓝 g)) (x : X) : Tendsto (f · x) l (𝓝 (g x)) :=
  ((continuous_id.eval_const x).tendsto _).comp hf

theorem Filter.Tendsto.coeFun {α : Type*} {l : Filter α} {f : α → F} {g : F}
    (hf : Tendsto f l (𝓝 g)) : Tendsto (fun a ↦ ⇑(f a)) l (𝓝 ⇑g) :=
  (continuous_id.coeFun.tendsto _).comp hf

nonrec theorem ContinuousAt.eval_const (hf : ContinuousAt f z) (x : X) : ContinuousAt (f · x) z :=
  hf.eval_const x

nonrec theorem ContinuousAt.coeFun (hf : ContinuousAt f z) : ContinuousAt (fun z ↦ ⇑(f z)) z :=
  hf.coeFun

nonrec theorem ContinuousWithinAt.eval_const (hf : ContinuousWithinAt f s z) (x : X) :
    ContinuousWithinAt (f · x) s z :=
  hf.eval_const x

nonrec theorem ContinuousWithinAt.coeFun (hf : ContinuousWithinAt f s z) :
    ContinuousWithinAt (fun z ↦ ⇑(f z)) s z :=
  hf.coeFun

theorem ContinuousOn.eval_const (hf : ContinuousOn f s) (x : X) : ContinuousOn (f · x) s :=
  fun z hz ↦ (hf z hz).eval_const x

theorem ContinuousOn.coeFun (hf : ContinuousOn f s) (x : X) : ContinuousOn (f · x) s :=
  fun z hz ↦ (hf z hz).eval_const x

end ContinuousEvalConst

class ContinuousEval (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
    [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  continuous_eval : Continuous fun fx : F × X ↦ fx.1 fx.2

export ContinuousEval (continuous_eval)

variable {F X Y Z : Type*} [FunLike F X Y]
  [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] [ContinuousEval F X Y]
  [TopologicalSpace Z] {f : Z → F} {g : Z → X} {s : Set Z} {z : Z}

@[continuity, fun_prop]
protected theorem Continuous.eval (hf : Continuous f) (hg : Continuous g) :
    Continuous fun z ↦ f z (g z) :=
  continuous_eval.comp (hf.prod_mk hg)

theorem ContinuousEval.of_continuous_forget {F' : Type*} [FunLike F' X Y] [TopologicalSpace F']
    {f : F' → F} (hc : Continuous f) (hf : ∀ g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEval F' X Y where
  continuous_eval := by simpa only [← hf] using hc.fst'.eval continuous_snd

instance (priority := 100) ContinuousEval.toContinuousMapClass : ContinuousMapClass F X Y where
  map_continuous _ := continuous_const.eval continuous_id

instance (priority := 100) ContinuousEval.toContinuousEvalConst : ContinuousEvalConst F X Y where
  continuous_eval_const _ := continuous_id.eval continuous_const

protected theorem Filter.Tendsto.eval {α : Type*} {l : Filter α} {f : α → F} {f₀ : F}
    {g : α → X} {x₀ : X} (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 x₀)) :
    Tendsto (fun a ↦ f a (g a)) l (𝓝 (f₀ x₀)) :=
  (ContinuousEval.continuous_eval.tendsto _).comp (hf.prod_mk_nhds hg)

protected nonrec theorem ContinuousAt.eval (hf : ContinuousAt f z) (hg : ContinuousAt g z) :
    ContinuousAt (fun z ↦ f z (g z)) z :=
  hf.eval hg

protected nonrec theorem ContinuousWithinAt.eval (hf : ContinuousWithinAt f s z)
    (hg : ContinuousWithinAt g s z) : ContinuousWithinAt (fun z ↦ f z (g z)) s z :=
  hf.eval hg

protected theorem ContinuousOn.eval (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun z ↦ f z (g z)) s :=
  fun z hz ↦ (hf z hz).eval (hg z hz)
