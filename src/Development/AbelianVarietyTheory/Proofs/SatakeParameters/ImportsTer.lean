module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactThird

@[expose] public section

namespace GlobalTheory.FiniteIndexSubgroup

open NumberField

private theorem exists_ne_zero_smul_mem_of_mem_span' {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    ∀ x ∈ Submodule.span E (L : Set (Fin n → E)), ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • x ∈ L := by
  first
  | exact @_root_.Bl.general_b_fact_third_alt.goal1
  | exact _root_.Bl.general_b_fact_third_alt.goal1
  | (apply _root_.Bl.general_b_fact_third_alt.goal1 <;> assumption)
  | (intros; apply _root_.Bl.general_b_fact_third_alt.goal1 <;> assumption)
  | (intros; apply @_root_.Bl.general_b_fact_third_alt.goal1 <;> first | assumption | infer_instance)
  | (intros; exact _root_.Bl.general_b_fact_third_alt.goal1 ..)

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E), ∃ (ν : NumberField.RingOfIntegers E), ν ≠ (0 : NumberField.RingOfIntegers E) ∧ ν • y ∈ L := by
  intro E _ _ n L hL y
  exact exists_ne_zero_smul_mem_of_mem_span' L y (by rw [hL]; exact Submodule.mem_top)

end GlobalTheory.FiniteIndexSubgroup
