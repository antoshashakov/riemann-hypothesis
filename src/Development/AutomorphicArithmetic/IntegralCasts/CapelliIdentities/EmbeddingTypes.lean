module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.Reformulated.B.EmbeddingTypes.core {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (L : Submodule R V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ s ∈ nonZeroDivisors R, s • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ y hy
  exact ⟨t, t.2, by simpa [Submonoid.smul_def] using ht⟩

theorem UpperTheory.Reformulated.B.EmbeddingTypes.exists_smul_mem_base_lattice_alt :
    ∀ (D : Formalism.BasicNotions.D7) (j : ℕ) (y : (D.sp.W j).V),
    ∃ s ∈ nonZeroDivisors (NumberField.RingOfIntegers D.host.E),
      s • y ∈
        (D.sp.W
            j).L0 := by
  intro D j y
  classical
  let S := D.sp.W j
  have hspan : Submodule.span D.host.E (S.L0 : Set S.V) = ⊤ := by
    exact S.span_baseLattice_eq_top
  exact UpperTheory.Reformulated.B.EmbeddingTypes.core (K := D.host.E) _ hspan y
