module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace LengthLayersP

section General

variable {O : Type} [CommRing O]

theorem length_eq_add_of_le {X : Type} [AddCommGroup X] [Module O X] {U V : Submodule O X}
    (h : U ≤ V) :
    Module.length O ↥V = Module.length O ↥U + Module.length O (↥V ⧸ U.comap V.subtype) := by
  rw [Module.length_eq_add_of_exact (U.comap V.subtype).subtype (U.comap V.subtype).mkQ
    Subtype.val_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
    (Submodule.comapSubtypeEquivOfLe h).length_eq]

theorem length_quot_eq_add {X : Type} [AddCommGroup X] [Module O X] {U V : Submodule O X}
    (h : U ≤ V) :
    Module.length O (X ⧸ U) = Module.length O ↥(V.map U.mkQ) + Module.length O (X ⧸ V) := by
  rw [Module.length_eq_add_of_exact (V.map U.mkQ).subtype (V.map U.mkQ).mkQ
    Subtype.val_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
    (Submodule.quotientQuotientEquivQuotient U V h).length_eq]

end General

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem length_residue (π : O) (hπ : Irreducible π) :
    Module.length O (O ⧸ Ideal.span {π}) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  exact (PrincipalIdealRing.isMaximal_of_irreducible hπ).out

theorem length_span_singleton_le (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] : ∀ (s : ℕ) (x : X), π ^ s • x = 0 → Module.length O ↥(O ∙ x) ≤ s := by
  intro s x hx
  let f := LinearMap.toSpanSingleton O X x
  have hker : IsLocalRing.maximalIdeal O ^ s ≤ LinearMap.ker f := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
      LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact hx
  let F := (IsLocalRing.maximalIdeal O ^ s).liftQ f hker
  have hr : F.range = O ∙ x := by
    dsimp only [F, f]
    rw [Submodule.range_liftQ, LinearMap.range_toSpanSingleton]
  rw [← hr, ← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O s]
  exact Module.length_le_of_surjective F.rangeRestrict F.surjective_rangeRestrict

end DVR

section Main

variable {O : Type} [CommRing O]

end Main

end LengthLayersP

end Formalism.G0
