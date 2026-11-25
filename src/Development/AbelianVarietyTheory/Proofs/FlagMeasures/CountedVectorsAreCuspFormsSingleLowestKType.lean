module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalOfConvolutionFixedModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepresentativeBoundedEvaluationStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanishStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorIsCuspForm

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RowCuspKType

private theorem one_mem_Kg_flag_measures (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · show (1 : I.Gf) ∈ I.Kset
    simp only [AutInst.Kset, Set.mem_ofPred_eq, OneMemClass.coe_one]
    exact one_mem _
  · simp only [AutInst.fmat, OneMemClass.coe_one, Units.val_one, sub_self, Matrix.zero_mulVec, smul_zero]

theorem level_comp_Re (B : RowsAut) (k : B.I.Gf) (hk : k ∈ B.I.Kg B.g) (hg : 1 ≤ B.g) :
    (B.R (1, k)).comp B.Re = B.Re := GlobalTheory.RowCusp.level_comp_Re B k hk hg

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hn : 1 ≤ B.I.n)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (hl : LocDec B h) :
    Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hb, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hcond : ∀ v, rkR (B.I.ε v) = 0 ∨
      8 * Real.sqrt (rkR (B.I.ε v)) * (0 + 4 * B.I.n * rkR (B.I.ε v)) < h := by
    intro v
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with h0 | hpos
    · exact Or.inl h0
    · right
      have hq : (0 : ℝ) < (rkR (B.I.ε v) : ℝ) := by exact_mod_cast hpos
      have hnr : (1 : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hn
      have hpow : ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
          = Real.sqrt (rkR (B.I.ε v)) * (rkR (B.I.ε v) : ℝ) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num,
          Real.rpow_add hq, Real.rpow_one]
      have hs : 0 < Real.sqrt (rkR (B.I.ε v)) := Real.sqrt_pos.mpr hq
      have hv := hh v
      rw [hpow] at hv
      have hpos' : 0 < Real.sqrt (rkR (B.I.ε v)) * (rkR (B.I.ε v) : ℝ) * (B.I.n : ℝ) := by positivity
      nlinarith
  have hI := hi 0 le_rfl hcond
  simp only [zero_mul, Real.exp_zero, mul_one] at hI
  exact hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

theorem row_isCuspFn : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  intro B d h hd hK hg hh hl hbig T hT A hA
  rcases Nat.eq_zero_or_pos B.I.n with hn0 | hnpos
  · intro W hW
    have : IsEmpty (Fin B.I.n) := by rw [hn0]; infer_instance
    exact absurd (Submodule.eq_bot_of_subsingleton) hW.1
  have hn : 1 ≤ B.I.n := hnpos
  have hint := integrable_ph B d h hd hn hh hl
  obtain ⟨-, hcomm, -, hT'⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hfix : T (A (B.tens B.w)) = A (B.tens B.w) := (hT' T hT).2.1 A hA
  obtain ⟨A₀, hA₀, hAe⟩ := Submodule.mem_map.mp hA
  have hAe' : A = B.Re.comp A₀ := by rw [← hAe]; rfl
  subst hAe'
  have hA₀' : ∀ g : B.I.Ginf, A₀.comp (B.σs g) = (B.R (g, 1)).comp A₀ := hA₀
  have hhom : B.Re.comp A₀ ∈ B.I.HomS B.σs B.μf B.fund B.R := by
    show ∀ g : B.I.Ginf, (B.Re.comp A₀).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A₀)
    intro g
    rw [ContinuousLinearMap.comp_assoc, hA₀' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ B.I.Kg B.g, B.R (1, k) ((B.Re.comp A₀) (B.tens B.w)) = (B.Re.comp A₀) (B.tens B.w) := by
    intro k hk
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re,
      level_comp_Re B k hk hg]
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_continuousRepresentative_bounded_evaluation B d hd hK hn hg
  obtain ⟨f, hf, hfb⟩ := hC _ hhom hlev
  have hvan := GlobalTheory.T.realUnipotent_integral_discreteSeries_vanish B d h hd hK hl hh
  refine (GlobalTheory.T.cuspidal_of_convolution_fixed_moderate_growth B d h hd hvan hl hbig T hT _ f (C * ‖(B.Re.comp A₀) (B.tens B.w)‖) ?_ hf ?_).2
  · simpa using hfix
  · intro x
    exact (hfb x).trans_eq (by ring)

end GlobalTheory.RowCuspKType
