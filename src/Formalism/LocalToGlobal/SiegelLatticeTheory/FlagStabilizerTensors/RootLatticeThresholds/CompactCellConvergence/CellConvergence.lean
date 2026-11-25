module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.MsetOfClosed
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpOrbOfAmpDD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.EtEquiv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.GrowthSide
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.OrbitIdentity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.PairMajInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.PairMeasBad
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.ClosedExistsOfCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv

@[expose] public section

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

def gProxy (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (x : PairSp k r) : ℝ :=
  Formalism.FourierDecayAlt.B.gN (Hpk k r * (Matrix.of x.1.1)ᴴ * Hpk k r * (Hpk k r * (Matrix.of x.1.2)ᴴ * Hpk k r) * γ *
    Matrix.of x.2.2 * Matrix.of x.2.1) ^ (-b)

theorem gProxy_meas (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) :
    Measurable (gProxy (k := k) (r := r) γ b) := by
  unfold gProxy
  apply Measurable.pow_const
  apply Continuous.measurable
  unfold Formalism.FourierDecayAlt.B.gN
  fun_prop

theorem gProxy_eq (L : LocBessel k r) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ)
    {x : PairSp k r} (hx : Good L x) : gProxy γ b x = Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b x := by
  obtain ⟨h12, h22, h11, h21⟩ := hx
  have e11 := uh_inv_eq (Formalism.L2.SG.Pf.WFL.Sset_sub_UH (uw_in_sset _ h11))
  have e12 := uh_inv_eq (Formalism.L2.SG.Pf.WFL.Sset_sub_UH (n_in_sset L.z h12))
  simp only [gProxy, Formalism.MainNotions.S.Pv.AmpDD.pairMaj, e11, e12]

private theorem gProxy_nonneg (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (x : PairSp k r) :
    0 ≤ gProxy γ b x := by
  unfold gProxy
  exact Real.rpow_nonneg (Formalism.FourierDecayAlt.P.gN_nonneg_bessel_integrability _) _

theorem cell_convergence : Formalism.MainNotions.S.Pv.AmpDD.CellConv :=
  _root_.GlobalTheory.CellMaj.cellConv

end Formalism.MainNotions.S.Pv.AmpDDPf.CC

theorem Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence : Formalism.MainNotions.S.Pv.AmpDD.CellConv :=
  Formalism.MainNotions.S.Pv.AmpDDPf.CC.cell_convergence
