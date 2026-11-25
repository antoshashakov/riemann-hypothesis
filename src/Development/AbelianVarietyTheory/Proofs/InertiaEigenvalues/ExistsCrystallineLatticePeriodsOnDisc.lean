module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPeriodMatrixOverAcris
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysLatticeBasisMemSumDeRhamFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeBasisSpanInvariants
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscPeriodDataOfAcrisPeriods
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusLatticeGeneratorsDdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusMatrixCrystallineModuleOverWitt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleInvariantPeriodMatrixBcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModificationOfFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
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

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.SeedExists

theorem exists_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ),
    (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T),
    Nonempty (Seed bk d (fun g => LinearMap.toMatrix b b (actT L g)) τ) := by
  intro l _ K bk τ hτ P AI hstd V _ _ _ _ _ _ _ ρ L _ hcrys d b
  obtain ⟨T⟩ := hstd
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  set ρm : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l] := fun g => LinearMap.toMatrix b b (actT L g) with hρm
  have hv0 := _root_.GlobalTheory.CrisCoord.lattice_basis_span_invariants l K P AI T V ρ L hcrys d b
  obtain ⟨U, U', hUU', hU⟩ := _root_.GlobalTheory.Per.PerMat.exists_invertible_invariant l K P AI T d ρm hv0
  obtain ⟨hInvB, hInvdR⟩ := _root_.GlobalTheory.MemLoc.fits_inv l P AI T C hC
  obtain ⟨c₁, c₃, F, F', hFF', hF⟩ := _root_.GlobalTheory.SeedF.frob_matrix l K bk C hInvB d ρm U U' hUU' hU
  obtain ⟨N₀, hN₀⟩ := _root_.GlobalTheory.CrisPeriods.periods_over_Acris l K P AI T C hC bk d ρm U U' hUU' hU c₁ F hF
  have hv2 := _root_.GlobalTheory.crysLattice_basis_mem_sum_fil_dR l K P AI T V ρ L hcrys d b
  obtain ⟨N, m, k, c, β, hN, hk, hUN, hUc, hβ, hUcβ⟩ :=
    _root_.GlobalTheory.BdRLatticeGens.exists_lattice_generators l K P AI T C hC hInvdR d ρm U U' hUU' hU hv2 N₀
  have hUU'ι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨c₂, X, X', hXX', hnp, hX, hX'⟩ :=
    _root_.GlobalTheory.BKModif.exists_modification_of_filtration l K bk C d (U.map C.ι) (U'.map C.ι) hUU'ι N m k c β hk (fun r s => hUN r s) hUc hβ hUcβ
  obtain ⟨Z, Z', hZ⟩ := hN₀ N hN X X' hX hX'
  exact _root_.GlobalTheory.BSP.seed_of_periods l K bk C τ hτ d ρm N c₁ c₂ c₃ F F' X X' hFF' hXX' hnp Z Z' hZ

end GlobalTheory.SeedExists
