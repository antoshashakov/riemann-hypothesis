module

public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGeneratorsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGeneratorsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXb
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiagStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOne
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverse
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBaseChangeCompatible
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpan
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminant
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegular
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDivisorFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameGenericRank
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameHeightFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTerm
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuation
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameOrderBound
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameUnitCriterion
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptIsVectorBundleRank
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMatStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.FMX.flagModelExists : GlobalTheory.CompanionTheory.Ar.Top.Given → PB.FlagModelExists := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 nd d bW bO hv hd
  classical
  have hVB := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.LL_isVB E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐
  have hcc := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO
  have hg : ∀ s, ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω (EE 𝔐)), IsTwistGen 𝔐.ξ (seg x₀) (LL 𝔐 s) m φ := fun s =>
    GlobalTheory.T.exists_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) 𝔐.tie 𝔐.all (hVB s)
  choose m n φ hφ using hg
  have hB : ∀ s, ∃ B : Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (n s)) Ω, B * aOf 𝔐 bW bO φ s = 1 := fun s =>
    GlobalTheory.T.frame_via_twisted_generators 𝔐.X Ω 𝔐.ξ (EE 𝔐) _ (seg x₀) (LL 𝔐 s) _ (VV 𝔐 s) (m s) (n s) (φ s) (cc 𝔐 bW bO s) 𝔐.tie (hVB s)
      (hφ s) (hcc s).1 (hcc s).2
  have hF : FormsOK 𝔐 bW bO m φ := ⟨hVB, hcc, hφ, hB⟩
  have hx₀ : ∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0 := by
    obtain ⟨c₀, hc₀⟩ := exists_inBlockChart 𝔐.tie ⟨genPt 𝔐.ξ, specializes_refl _⟩
    exact fun k => ⟨c₀ k, (hc₀ k).1⟩
  have ht := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hP := GlobalTheory.T.blkF_properStep_injective_blockDiag (CMType H) D.p D.q Ω K₀
  have hmod : ModelOK (aOf 𝔐 bW bO φ) x₀ m :=
    ⟨hP.1, hP.2.1, _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne _ _ _ Ω _ _ K₀ J₀ x₀ hx₀ hB,
      _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv _ _ _ Ω _ _ K₀ J₀ x₀, hP.2.2, _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag _ _ _ Ω, GlobalTheory.T.yv_eq_sum_minors_gMat _ _ _ Ω _ _ K₀ J₀ x₀,
      _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht⟩
  have hT := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod
  obtain ⟨Z, ξ', f, htie, hall, hdom, hsm⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF
  have hnorm := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF Z ξ' f htie hall hdom hsm
  obtain ⟨𝔐', e, j, -, hov, hR, hsp, hV⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HcptFlat.hodgeCpt_pull_smooth E H D l Xo c Y S Ω _ (algebraMap Ω _) K₀ _ J₀ _ x₀ _ 𝔐 Z ξ' f hall htie hnorm hdom hsm
  obtain ⟨Fl, hdeg, hfl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.exists_colFlags E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ d hF hd 𝔐' _ j hov hsp hV
  obtain ⟨xdeg, hroot, hdy⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ hF ht hmod 𝔐' _ j Fl hov hsp hV hfl
  let M := model (aOf 𝔐 bW bO φ) x₀ m hmod
  let 𝔐₁ : HodgeCpt Y S M.x := reTie 𝔐 (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) ht
  let tie : FlagTie M 𝔐₁ :=
    { eW := bW, eO := bO, frameW := fun q F h h' τ => (hT q F h h' τ).1, frameO := fun q F h h' τ => (hT q F h h' τ).2 }
  have hκ : ∀ k : K₀, ∀ r, M.blk r ≠ some (.inl k) := fun k r h => by
    change blkF (CMType H) D.p D.q K₀ r = _ at h
    unfold blkF at h
    split_ifs at h
    simpa using h
  let κ : K₀ → NonPluckerBlocks M.blk := fun k => ⟨.inl k, hκ k⟩
  let v : (Σ k, J₀ k) → Σ k, baseIdx (idx (p := D.p) (q := D.q) J₀ n) M.blk k := fun r => ⟨κ r.1, r.2⟩
  refine ⟨K₀ ⊕ StepIx (CMType H) D.p D.q, inferInstance, idx J₀ n, inferInstance, GenField Ω (rk (CMType H) D.p D.q),
    inferInstance, yv (aOf 𝔐 bW bO φ) x₀, M, 𝔐₁, tie, κ, v, RingHom.id Ω, 𝟙 𝔐.X, AddMonoidHom.id 𝔐.Li, 𝔐', Fl, xdeg,
    fun _ => 1, ⟨?_, fun _ => rfl, Function.bijective_id, inferInstanceAs (IsIso (𝟙 𝔐.X)), ?_, rfl, ?_⟩,
    ⟨hd, _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.DimBase.isArithVar_xb E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF ht hv, _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.hasSncBoundary_reTie E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ ht⟩,
    _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_flagModel E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 bW bO n m φ nd hF hv, ?_, hdeg⟩
  · refine ⟨fun a b h => Sum.inl_injective (congrArg (fun k => k.1) h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, i⟩ ⟨k', i'⟩ h
      have h1 : k = k' := Sum.inl_injective (congrArg (fun r => r.1.1) h)
      subst h1
      have h2 : HEq i i' := (Sigma.mk.inj_iff.1 h).2
      rw [eq_of_heq h2]
    · rintro ⟨_, i⟩ ⟨k, rfl⟩
      exact ⟨⟨k, i⟩, rfl⟩
  · exact HodgeOver.refl 𝔐
  · exact BasesOver.refl bW bO
  · refine ⟨⟨e.hom ≫ f, j, hov, hR, hV, hfl.1, hfl.2⟩, hroot, hdy, fun τ i => ?_⟩
    have h1 : detFac D.p i (M.g τ) = 1 := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat (CMType H) D.p D.q Ω τ i
    have h2 : M.lam (τ, i) = 1 := rfl
    rw [h1, h2]
    rcases M.blk (τ, i) with _ | b <;> simp
