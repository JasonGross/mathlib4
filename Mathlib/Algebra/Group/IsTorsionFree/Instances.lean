import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Algebra.Group.IsTorsionFree.Defs
import Mathlib.Algebra.Group.Pi.Basic

@[to_additive]
instance Prod.instIsMulTorsionFree {M N : Type*} [Monoid M] [Monoid N] [IsMulTorsionFree M]
    [IsMulTorsionFree N] : IsMulTorsionFree (M × N) where
  eq_one_of_pow_eq_one _x _n hxn hn :=
    Prod.ext (eq_one_of_pow_eq_one (congrArg Prod.fst hxn) hn)
      (eq_one_of_pow_eq_one (congrArg Prod.snd hxn) hn)

@[to_additive]
instance Pi.instIsMulTorsionFree {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, IsMulTorsionFree (M i)] : IsMulTorsionFree (∀ i, M i) where
  eq_one_of_pow_eq_one _x _n hxn hn := funext fun i ↦ eq_one_of_pow_eq_one (congrFun hxn i) hn

@[to_additive]
theorem Function.Injective.isMulTorsionFree {M N : Type*} [Monoid M] [Monoid N]
    [IsMulTorsionFree N] (f : M →* N) (hf : Function.Injective f) : IsMulTorsionFree M where
  eq_one_of_pow_eq_one _x _n hxn hn := hf <| by simpa [hn] using congrArg f hxn

@[to_additive]
instance Units.instIsMulTorsionFree {M : Type*} [Monoid M] [IsMulTorsionFree M] :
    IsMulTorsionFree Mˣ :=
  Units.ext.isMulTorsionFree (Units.coeHom M)