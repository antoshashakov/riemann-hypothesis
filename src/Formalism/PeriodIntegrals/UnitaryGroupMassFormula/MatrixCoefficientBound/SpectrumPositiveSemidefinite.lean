module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.PermRepApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Matrix Classical
open scoped ComplexOrder

namespace PI.GGMatBoundW

theorem spectrum_positive_semidefinite : SpecPSD := by
  intro X _ M c hM hev
  have psd (A : Matrix X X ℂ) (hA : A.IsHermitian)
      (h : ∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → A *ᵥ w = μ • w → ∃ r : ℝ, μ = r ∧ 0 ≤ r) :
      A.PosSemidef := by
    refine hA.posSemidef_iff_eigenvalues_nonneg.mpr fun j => ?_
    have hne := hA.eigenvectorBasis.orthonormal.ne_zero j
    obtain ⟨r, hr, h0⟩ := h _ (hA.eigenvalues j)
      (fun h0 => hne (by ext i; simpa using congrFun h0 i))
      (by rw [hA.mulVec_eigenvectorBasis j]; ext i; simp)
    exact h0.trans (Complex.ofReal_injective hr).ge
  have hN : ((c : ℂ) • (1 : Matrix X X ℂ) - M).IsHermitian :=
    IsHermitian.sub (by simp [IsHermitian, conjTranspose_smul]) hM
  refine ⟨psd M hM fun w μ hw h => ?_, psd _ hN fun w μ hw h => ?_⟩
  · obtain ⟨r, hr, h0, -⟩ := hev w μ hw h
    exact ⟨r, hr, h0⟩
  · obtain ⟨r, hr, -, hrc⟩ := hev w (c - μ) hw <| by
      rw [sub_smul, ← h, sub_mulVec, smul_mulVec, one_mulVec]; abel
    exact ⟨c - r, by push_cast; linear_combination -hr, by linarith⟩

end PI.GGMatBoundW
