/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Computability.Language

/-!
# Context-Free Grammars

This file contains the definition of a context-free grammar, which is a grammar that has a single
nonterminal symbol on the left-hand side of each rule.

## Main definitions
* `ContextFreeGrammar`: A context-free grammar.
* `ContextFreeGrammar.language`: A language generated by a given context-free grammar.

## Main theorems
* `Language.IsContextFree.reverse`: The class of context-free languages is closed under reversal.
-/

universe uT uN in
/-- Rule that rewrites a single nonterminal to any string (a list of symbols). -/
structure ContextFreeRule (T : Type uT) (N : Type uN) where
  /-- Input nonterminal a.k.a. left-hand side. -/
  input : N
  /-- Output string a.k.a. right-hand side. -/
  output : List (Symbol T N)

/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure ContextFreeGrammar.{uN,uT} (T : Type uT) where
  /-- Type of nonterminals. -/
  NT : Type uN
  /-- Initial nonterminal. -/
  initial : NT
  /-- Rewrite rules. -/
  rules : List (ContextFreeRule T NT)

universe uT uN
variable {T : Type uT}

namespace ContextFreeRule
variable {N : Type uN}

/-- Inductive definition of a single application of a given context-free rule `r` to a string `u`;
`r.Rewrites u v` means that the `r` sends `u` to `v` (there may be multiple such strings `v`). -/
inductive Rewrites (r : ContextFreeRule T N) : List (Symbol T N) → List (Symbol T N) → Prop
  /-- The replacement is at the start of the remaining string. -/
  | head (s : List (Symbol T N)) :
      r.Rewrites (Symbol.nonterminal r.input :: s) (r.output ++ s)
  /-- There is a replacement later in the string. -/
  | cons (x : Symbol T N) {s₁ s₂ : List (Symbol T N)} (hrs : Rewrites r s₁ s₂) :
      r.Rewrites (x :: s₁) (x :: s₂)

lemma Rewrites.exists_parts {r : ContextFreeRule T N} {u v : List (Symbol T N)}
    (hr : r.Rewrites u v) :
    ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
  induction hr with
  | head s =>
    use [], s
    simp
  | cons x _ ih =>
    rcases ih with ⟨p', q', rfl, rfl⟩
    use x :: p', q'
    simp

lemma rewrites_of_exists_parts (r : ContextFreeRule T N) (p q : List (Symbol T N)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
  induction p with
  | nil         => exact Rewrites.head q
  | cons d l ih => exact Rewrites.cons d ih

/-- Rule `r` rewrites string `u` is to string `v` iff they share both a prefix `p` and postfix `q`
such that the remaining middle part of `u` is the input of `r` and the remaining middle part
of `u` is the output of `r`. -/
theorem rewrites_iff {r : ContextFreeRule T N} (u v : List (Symbol T N)) :
    r.Rewrites u v ↔ ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q :=
  ⟨Rewrites.exists_parts, by rintro ⟨p, q, rfl, rfl⟩; apply rewrites_of_exists_parts⟩

/-- Add extra prefix to context-free rewriting. -/
lemma Rewrites.append_left {r : ContextFreeRule T N} {v w : List (Symbol T N)}
    (hvw : r.Rewrites v w) (p : List (Symbol T N)) : r.Rewrites (p ++ v) (p ++ w) := by
  rw [rewrites_iff] at *
  rcases hvw with ⟨x, y, hxy⟩
  use p ++ x, y
  simp_all

/-- Add extra postfix to context-free rewriting. -/
lemma Rewrites.append_right {r : ContextFreeRule T N} {v w : List (Symbol T N)}
    (hvw : r.Rewrites v w) (p : List (Symbol T N)) : r.Rewrites (v ++ p) (w ++ p) := by
  rw [rewrites_iff] at *
  rcases hvw with ⟨x, y, hxy⟩
  use x, y ++ p
  simp_all

end ContextFreeRule

namespace ContextFreeGrammar

/-- Given a context-free grammar `g` and strings `u` and `v`
`g.Produces u v` means that one step of a context-free transformation by a rule from `g` sends
`u` to `v`. -/
def Produces (g : ContextFreeGrammar.{uN} T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.Rewrites u v

/-- Given a context-free grammar `g` and strings `u` and `v`
`g.Derives u v` means that `g` can transform `u` to `v` in some number of rewriting steps. -/
abbrev Derives (g : ContextFreeGrammar.{uN} T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces

/-- Given a context-free grammar `g` and a string `s`
`g.Generates s` means that `g` can transform its initial nonterminal to `s` in some number of
rewriting steps. -/
def Generates (g : ContextFreeGrammar.{uN} T) (s : List (Symbol T g.NT)) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] s

/-- The language (set of words) that can be generated by a given context-free grammar `g`. -/
def language (g : ContextFreeGrammar.{uN} T) : Language T :=
  { w | g.Generates (List.map Symbol.terminal w) }

/-- A given word `w` belongs to the language generated by a given context-free grammar `g` iff
`g` can derive the word `w` (wrapped as a string) from the initial nonterminal of `g` in some
number of steps. -/
@[simp]
lemma mem_language_iff (g : ContextFreeGrammar.{uN} T) (w : List T) :
    w ∈ g.language ↔ g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w) := by
  rfl

variable {g : ContextFreeGrammar.{uN} T}

@[refl]
lemma Derives.refl (w : List (Symbol T g.NT)) : g.Derives w w :=
  Relation.ReflTransGen.refl

lemma Produces.single {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) : g.Derives v w :=
  Relation.ReflTransGen.single hvw

@[trans]
lemma Derives.trans {u v w : List (Symbol T g.NT)} (huv : g.Derives u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  Relation.ReflTransGen.trans huv hvw

lemma Derives.trans_produces {u v w : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hvw : g.Produces v w) :
    g.Derives u w :=
  huv.trans hvw.single

lemma Produces.trans_derives {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  huv.single.trans hvw

lemma Derives.eq_or_head {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.Derives v w :=
  Relation.ReflTransGen.cases_head huw

lemma Derives.eq_or_tail {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Derives u v ∧ g.Produces v w :=
  (Relation.ReflTransGen.cases_tail huw).casesOn (Or.inl ∘ Eq.symm) Or.inr

/-- Add extra prefix to context-free producing. -/
lemma Produces.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (p ++ v) (p ++ w) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_left p⟩

/-- Add extra postfix to context-free producing. -/
lemma Produces.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (v ++ p) (w ++ p) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_right p⟩

/-- Add extra prefix to context-free deriving. -/
lemma Derives.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (p ++ v) (p ++ w) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to context-free deriving. -/
lemma Derives.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (v ++ p) (w ++ p) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_right p

end ContextFreeGrammar

/-- Context-free languages are defined by context-free grammars. -/
def Language.IsContextFree (L : Language T) : Prop :=
  ∃ g : ContextFreeGrammar.{uT} T, g.language = L

section closure_reversal

/-- Rules for a grammar for a reversed language. -/
def ContextFreeRule.reverse {N : Type uN} (r : ContextFreeRule T N) : ContextFreeRule T N :=
  ⟨r.input, r.output.reverse⟩

/-- Grammar for a reversed language. -/
def ContextFreeGrammar.reverse (g : ContextFreeGrammar T) : ContextFreeGrammar T :=
  ⟨g.NT, g.initial, g.rules.map .reverse⟩

lemma ContextFreeRule.reverse_involutive {N : Type uN} :
    Function.Involutive (@ContextFreeRule.reverse T N) := by
  intro x
  simp [ContextFreeRule.reverse]

lemma ContextFreeGrammar.reverse_involutive :
    Function.Involutive (@ContextFreeGrammar.reverse T) := by
  intro x
  simp [ContextFreeGrammar.reverse, ContextFreeRule.reverse_involutive]

lemma ContextFreeGrammar.reverse_derives (g : ContextFreeGrammar T) {s : List (Symbol T g.NT)}
    (hgs : g.reverse.Derives [Symbol.nonterminal g.reverse.initial] s) :
    g.Derives [Symbol.nonterminal g.initial] s.reverse := by
  induction hgs with
  | refl =>
    rw [List.reverse_singleton]
    apply ContextFreeGrammar.Derives.refl
  | tail _ orig ih =>
    apply ContextFreeGrammar.Derives.trans_produces ih
    obtain ⟨r, rin, rewr⟩ := orig
    simp only [ContextFreeGrammar.reverse, List.mem_map] at rin
    obtain ⟨r₀, rin₀, rfl⟩ := rin
    refine ⟨r₀, rin₀, ?_⟩
    rw [ContextFreeRule.rewrites_iff] at rewr ⊢
    rcases rewr with ⟨p, q, rfl, rfl⟩
    use q.reverse, p.reverse
    simp [ContextFreeRule.reverse]

lemma ContextFreeGrammar.reverse_mem_language_of_mem_reverse_language (g : ContextFreeGrammar T)
    {w : List T} (hgw : w ∈ g.reverse.language) :
    w.reverse ∈ g.language := by
  convert g.reverse_derives hgw
  simp [List.map_reverse]

lemma ContextFreeGrammar.mem_reverse_language_iff_reverse_mem_language (g : ContextFreeGrammar T)
    (w : List T) :
    w ∈ g.reverse.language ↔ w.reverse ∈ g.language := by
  refine ⟨reverse_mem_language_of_mem_reverse_language _, fun hw => ?_⟩
  rw [← ContextFreeGrammar.reverse_involutive g] at hw
  rw [← List.reverse_reverse w]
  exact g.reverse.reverse_mem_language_of_mem_reverse_language hw

/-- The class of context-free languages is closed under reversal. -/
theorem Language.IsContextFree.reverse (L : Language T) :
    L.IsContextFree → L.reverse.IsContextFree :=
  fun ⟨g, hg⟩ => ⟨g.reverse, hg ▸ Set.ext g.mem_reverse_language_iff_reverse_mem_language⟩

end closure_reversal

section embed_project

/-! This section contains only auxiliary constructions that will shorten upcoming proofs of
closure properties. When combining several grammars together, we usually want to take a sum type of
their nonterminal types and embed respective nonterminals to this sum type. We subsequently show
that the resulting grammar preserves derivations of those strings that may contain any terminals but
only the proper nonterminals. The embedding operation must be injective. The projection operation
must be injective on those symbols where it is defined. -/

/-- Mapping `Symbol` when it is a nonterminal. -/
def Symbol.map {N₀ N : Type*} (f : N₀ → N) : Symbol T N₀ → Symbol T N
  | Symbol.terminal t => Symbol.terminal t
  | Symbol.nonterminal n => Symbol.nonterminal (f n)

/-- Mapping `Symbol` when it is a nonterminal; may return `none`. -/
def Symbol.filterMap {N₀ N : Type*} (f : N → Option N₀) : Symbol T N → Option (Symbol T N₀)
  | Symbol.terminal t => some (Symbol.terminal t)
  | Symbol.nonterminal n => Option.map Symbol.nonterminal (f n)

/-- Map the type of nonterminal symbols of a `ContextFreeRule` . -/
def ContextFreeRule.map {N₀ N : Type*} (r : ContextFreeRule T N₀) (f : N₀ → N) :
    ContextFreeRule T N :=
  ⟨f r.input, r.output.map (Symbol.map f)⟩

/-- A pair of `ContextFreeGrammar`s with maps between their nonterminal types that work,
roughly speaking, in a good way. -/
structure EmbeddedContextFreeGrammar (T : Type uT) where
  /-- The smaller grammar. -/
  g₀ : ContextFreeGrammar.{uN} T
  /-- The bigger grammar. -/
  g : ContextFreeGrammar.{uN} T
  /-- Mapping nonterminals from the smaller type to the bigger type. -/
  embedNT : g₀.NT → g.NT
  /-- Mapping nonterminals from the bigger type to the smaller type. -/
  projectNT : g.NT → Option g₀.NT
  /-- The former map is injective. -/
  embed_inj : Function.Injective embedNT
  /-- The latter map is injective where defined. -/
  project_inj : ∀ x y, projectNT x = projectNT y → x = y ∨ projectNT x = none
  /-- The two mappings are essentially inverses. -/
  projectNT_embedNT : ∀ n₀ : g₀.NT, projectNT (embedNT n₀) = some n₀
  /-- Each rule of the smaller grammar has a corresponding rule in the bigger grammar. -/
  embed_mem_rules : ∀ r : ContextFreeRule T g₀.NT, r ∈ g₀.rules → r.map embedNT ∈ g.rules
  /-- Each rule of the bigger grammar whose input nonterminal the smaller grammar recognizes
  has a corresponding rule in the smaller grammar. -/
  preimage_of_rules :
    ∀ r : ContextFreeRule T g.NT,
      r ∈ g.rules → ∀ n₀ : g₀.NT,
        embedNT n₀ = r.input → ∃ r₀ ∈ g₀.rules, r₀.map embedNT = r

lemma EmbeddedContextFreeGrammar.projectNT_inverse_embedNT (G : EmbeddedContextFreeGrammar T) :
    ∀ x : G.g.NT, (∃ n₀, G.projectNT x = some n₀) → (Option.map G.embedNT (G.projectNT x) = x) := by
  intro x ⟨n₀, hx⟩
  rw [hx, Option.map_some']
  apply congr_arg
  by_contra hnx
  cases (G.projectNT_embedNT n₀ ▸ G.project_inj x (G.embedNT n₀)) hx with
  | inl case_valu => exact hnx case_valu.symm
  | inr case_none => exact Option.noConfusion (hx ▸ case_none)

/-- Production by `G.g₀` can be mirrored by `G.g` production. -/
lemma EmbeddedContextFreeGrammar.produces_map {G : EmbeddedContextFreeGrammar T}
    {w₁ w₂ : List (Symbol T G.g₀.NT)} (hG : G.g₀.Produces w₁ w₂) :
    G.g.Produces (w₁.map (Symbol.map G.embedNT)) (w₂.map (Symbol.map G.embedNT)) := by
  rcases hG with ⟨r, rin, hr⟩
  rcases hr.exists_parts with ⟨u, v, bef, aft⟩
  refine ⟨r.map G.embedNT, G.embed_mem_rules r rin, ?_⟩
  rw [ContextFreeRule.rewrites_iff]
  use u.map (Symbol.map G.embedNT), v.map (Symbol.map G.embedNT)
  constructor
  · simpa only [List.map_append] using congr_arg (List.map (Symbol.map G.embedNT)) bef
  · simpa only [List.map_append] using congr_arg (List.map (Symbol.map G.embedNT)) aft

/-- Derivation by `G.g₀` can be mirrored by `G.g` derivation. -/
lemma EmbeddedContextFreeGrammar.derives_map {G : EmbeddedContextFreeGrammar T}
    {w₁ w₂ : List (Symbol T G.g₀.NT)} (hG : G.g₀.Derives w₁ w₂) :
    G.g.Derives (w₁.map (Symbol.map G.embedNT)) (w₂.map (Symbol.map G.embedNT)) := by
  induction hG with
  | refl => rfl
  | tail _ orig ih => exact ih.trans_produces (produces_map orig)

/-- A `Symbol` is good iff it is one of those nonterminals that result from projecting or it is any
terminal. -/
def EmbeddedContextFreeGrammar.Good {G : EmbeddedContextFreeGrammar T} : Symbol T G.g.NT → Prop
  | Symbol.terminal _ => True
  | Symbol.nonterminal n => ∃ n₀ : G.g₀.NT, G.projectNT n = n₀

/-- A string is good iff every `Symbol` in it is good. -/
def EmbeddedContextFreeGrammar.GoodString {G : EmbeddedContextFreeGrammar T}
    (s : List (Symbol T G.g.NT)) : Prop :=
  ∀ a ∈ s, Good a

lemma EmbeddedContextFreeGrammar.singletonGoodString {G : EmbeddedContextFreeGrammar T}
    {s : Symbol T G.g.NT} (hs : G.Good s) : G.GoodString [s] := by
  simpa [GoodString] using hs

/-- Production by `G.g` can be mirrored by `G.g₀` production if the first word does not contain
any nonterminals that `G.g₀` lacks. -/
lemma EmbeddedContextFreeGrammar.produces_filterMap {G : EmbeddedContextFreeGrammar T}
    {w₁ w₂ : List (Symbol T G.g.NT)} (hG : G.g.Produces w₁ w₂) (hw₁ : GoodString w₁) :
    G.g₀.Produces
      (w₁.filterMap (Symbol.filterMap G.projectNT))
      (w₂.filterMap (Symbol.filterMap G.projectNT)) ∧
    GoodString w₂ := by
  rcases hG with ⟨r, rin, hr⟩
  rcases hr.exists_parts with ⟨u, v, bef, aft⟩
  rw [bef] at hw₁
  obtain ⟨n₀, hn₀⟩ : Good (Symbol.nonterminal r.input) := by apply hw₁; simp
  rcases G.preimage_of_rules r rin n₀ (by
    simpa [G.projectNT_inverse_embedNT r.input ⟨n₀, hn₀⟩, Option.map_some'] using
      congr_arg (Option.map G.embedNT) hn₀.symm)
    with ⟨r₀, hr₀, hrr₀⟩
  constructor
  · refine ⟨r₀, hr₀, ?_⟩
    rw [ContextFreeRule.rewrites_iff]
    use u.filterMap (Symbol.filterMap G.projectNT), v.filterMap (Symbol.filterMap G.projectNT)
    have correct_inverse : Symbol.filterMap (T := T) G.projectNT ∘ Symbol.map G.embedNT =
        Option.some := by
      ext1 x
      cases x
      · rfl
      rw [Function.comp_apply]
      simp only [Symbol.filterMap, Symbol.map, Option.map_eq_some', Symbol.nonterminal.injEq]
      rw [exists_eq_right]
      apply G.projectNT_embedNT
    constructor
    · have middle :
        List.filterMap (Symbol.filterMap (T := T) G.projectNT)
          [Symbol.nonterminal (G.embedNT r₀.input)] =
          [Symbol.nonterminal r₀.input] := by
        simp [Symbol.filterMap, G.projectNT_embedNT]
      simpa only [List.filterMap_append, ContextFreeRule.map, ← hrr₀, middle]
        using congr_arg (List.filterMap (Symbol.filterMap G.projectNT)) bef
    · simpa only [List.filterMap_append, ContextFreeRule.map,
          List.filterMap_map, List.filterMap_some, ← hrr₀, correct_inverse]
        using congr_arg (List.filterMap (Symbol.filterMap G.projectNT)) aft
  · rw [aft, ← hrr₀]
    simp only [GoodString, List.forall_mem_append] at hw₁ ⊢
    refine ⟨⟨hw₁.left.left, ?_⟩, hw₁.right⟩
    intro a ha
    cases a
    · simp [Good]
    dsimp only [ContextFreeRule.map] at ha
    rw [List.mem_map] at ha
    rcases ha with ⟨s, -, hs⟩
    rw [← hs]
    cases s with
    | terminal _ => exact False.elim (Symbol.noConfusion hs)
    | nonterminal s' => exact ⟨s', G.projectNT_embedNT s'⟩

lemma EmbeddedContextFreeGrammar.derives_filterMap_aux {G : EmbeddedContextFreeGrammar T}
    {w₁ w₂ : List (Symbol T G.g.NT)} (hG : G.g.Derives w₁ w₂) (hw₁ : GoodString w₁) :
    G.g₀.Derives
      (w₁.filterMap (Symbol.filterMap G.projectNT))
      (w₂.filterMap (Symbol.filterMap G.projectNT)) ∧
    GoodString w₂ := by
  induction hG with
  | refl => exact ⟨by rfl, hw₁⟩
  | tail _ orig ih =>
    have both := produces_filterMap orig ih.right
    exact ⟨ContextFreeGrammar.Derives.trans_produces ih.left both.left, both.right⟩

/-- Derivation by `G.g` can be mirrored by `G.g₀` derivation if the starting word does not contain
any nonterminals that `G.g₀` lacks. -/
lemma EmbeddedContextFreeGrammar.derives_filterMap (G : EmbeddedContextFreeGrammar T)
    {w₁ w₂ : List (Symbol T G.g.NT)} (hG : G.g.Derives w₁ w₂) (hw₁ : GoodString w₁) :
    G.g₀.Derives
      (w₁.filterMap (Symbol.filterMap G.projectNT))
      (w₂.filterMap (Symbol.filterMap G.projectNT)) :=
  (derives_filterMap_aux hG hw₁).left

end embed_project
