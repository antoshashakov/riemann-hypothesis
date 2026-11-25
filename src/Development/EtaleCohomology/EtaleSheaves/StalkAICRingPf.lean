module

public import Development.EtaleCohomology.EtaleSheaves.FibreEqvPf
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure.AicLoc

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StalkAICRingPf

theorem aic_loc {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : AIC R) : AIC S := LateralTheory.E.BaseAICPf.Loc.aic_loc M hR

theorem StalkAICRing_of : LateralTheory.E.FibreEqvPf.StalkAICRing := by
  intro S hS x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let _ := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact aic_loc (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (hS.2 U hU ⟨x, hxU⟩)

end LateralTheory.E.StalkAICRingPf
