module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphism
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIdealEqMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaLamEqToB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLamGaloisEquivariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLatticeBase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphism
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompat
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatFinal
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

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Lat

theorem dp_of_char {K A B A' B' : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra K B']
    {I : Ideal A} {I' : Ideal A'} {J : Ideal B} {J' : Ideal B'} (δ : DividedPowers J) (δ' : DividedPowers J') (ι : A →+* B)
    (ι' : A' →+* B') (s : A →+* A') (g : B →+* B') (hJ : J = I.map ι) (hJ' : J' = I'.map ι') (hs : I.map s ≤ I')
    (h : ∀ a, g (ι a) = ι' (s a)) : IsDPMorphism δ δ' g := by
  have h1 : J.map g ≤ J' := by
    rw [hJ, hJ', Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    change g (ι a) ∈ I'.map ι'
    rw [h]
    exact Ideal.mem_map_of_mem _ (hs (Ideal.mem_map_of_mem _ ha))
  refine ⟨h1, fun {n} a ha => ?_⟩
  have hu : IsUnit (n.factorial : B') := by
    have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 n.factorial_ne_zero) : IsUnit (n.factorial : K)).map (algebraMap K B')
    rwa [map_natCast] at this
  refine hu.mul_left_cancel ?_
  rw [δ'.factorial_mul_dpow_eq_pow (h1 (Ideal.mem_map_of_mem _ ha)), ← map_natCast g, ← map_mul, δ.factorial_mul_dpow_eq_pow ha, map_pow]

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem levHyp_ex [FiniteDimensional ℚ_[l] K] : ∃ M : ℕ, LevHyp l K M :=
  (_root_.GlobalTheory.CompanionTheory.LatCOK.exists_uniform_mem_sub l K).imp fun M h => ⟨h, _root_.GlobalTheory.CompanionTheory.LatCris.cris_in l M, _root_.GlobalTheory.CompanionTheory.LatCHc.hc_k l M, _root_.GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap l K,
    fun k g => _root_.GlobalTheory.CompanionTheory.LatGal.gal_mem_sub l K M k g _, _root_.GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub l M⟩

theorem lev_σ_ι (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (a : (lev h k).A) :
    (lev h k).ι ((lev h k).σA g a) = (lev h k).σB g ((lev h k).ι a) :=
  ι_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) a

theorem lev_good (h : LevHyp l K M) (k : ℕ) (hk : 1 ≤ k) : (lev h k).Good := by
  exact {
    pos := hk
    lat := _root_.GlobalTheory.CompanionTheory.LatCBase.latBase_lev h k hk
    toB_surj := _root_.GlobalTheory.CompanionTheory.LatLevels.toB_surjective h k
    toB_ker := _root_.GlobalTheory.CompanionTheory.LatC.lev_toB_ker h k
    toB_K := _root_.GlobalTheory.CompanionTheory.LatC.toB_on_K h k
    ι_inj := ι_injective (fk l k) (xi0 l) l M
    ι_dp := dp_ι (fk l k) (xi0 l) l M (h.hc k)
    ι_I := rfl
    IB_eq := _root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h k
    ι_O := _root_.GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK h k
    ι_lam := _root_.GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB h k
    σB_toB := _root_.GlobalTheory.CompanionTheory.LatC.sigmaB_toB h k
    σ_ι := lev_σ_ι h k
    σ_lam := _root_.GlobalTheory.CompanionTheory.LatCSig.sig_lam h k
    σ_O := _root_.GlobalTheory.CompanionTheory.LatC.sigA_fix h k
    σ_dp := _root_.GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism h k
    σB_dp g := dp_of_char (K := K) (lev h k).γB (lev h k).γB (lev h k).ι (lev h k).ι ((lev h k).σA g) ((lev h k).σB g)
      (_root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h k) (_root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h k) (_root_.GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism h k g).1 fun a => (lev_σ_ι h k g a).symm
    σB_K := _root_.GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K h k
    pdP_B := _root_.GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow h k
  }

theorem dk_pk (k : ℕ) (x : BdRp l) : dk l k (pk l (k + 1) x) = pk l k x := rfl

theorem sys_dι (h : LevHyp l K M) (m : ℕ) (a : ((levSys h).L (m + 1)).A) :
    (levSys h).dB m (((levSys h).L (m + 1)).ι a) = ((levSys h).L m).ι ((levSys h).dA m a) :=
  (ι_map (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1)) (h.dIn (m + 1)) a).symm

theorem levSys_good (h : LevHyp l K M) : (levSys h).Good := by
  exact {
    lev m := lev_good h (m + 1) (Nat.le_add_left 1 m)
    dB_toB m x := dk_pk (m + 1) (pInv l x)
    dι := sys_dι h
    dlam m c := Subtype.ext (dk_pk (m + 1) (ACris.iota ℂ_[l] l c))
    dO m a := Subtype.ext (dk_pk (m + 1) (kP l K a))
    dK m k := dk_pk (m + 1) (kP l K k)
    ddp := _root_.GlobalTheory.CompanionTheory.LatC.levSys_ddp h
    ddpB m := dp_of_char (K := K) ((levSys h).L (m + 1)).γB ((levSys h).L m).γB ((levSys h).L (m + 1)).ι ((levSys h).L m).ι
      ((levSys h).dA m) ((levSys h).dB m) (_root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h (m + 2)) (_root_.GlobalTheory.CompanionTheory.LatC.lev_IB_eq_map h (m + 1)) (_root_.GlobalTheory.CompanionTheory.LatC.levSys_ddp h m).1 (sys_dι h m)
    dσ := _root_.GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA h
    dσB := _root_.GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB h
    cpl := _root_.GlobalTheory.CompanionTheory.LatC.levSys_existsUnique h
  }

theorem levSys_ex [FiniteDimensional ℚ_[l] K] : ∃ S : Kap.LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK :=
  (levHyp_ex (l := l) (K := K)).elim fun _ h => ⟨levSys h, levSys_good h, fun m => _root_.GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I h (m + 1)⟩

end CrystallineSemistableComparison.HT
