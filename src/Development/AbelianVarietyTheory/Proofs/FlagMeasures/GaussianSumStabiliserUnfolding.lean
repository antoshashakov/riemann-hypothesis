module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicOrthogonalStabilizerEmbedding
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMassOneCutoffDoubleCosetIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrou
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthComplementUnitVectorSameFields
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImageRationalOrthComplementUnitaryEqRationalStab
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingOfCongruenceSubgroupsConj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityUnfoldSubgroup
public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralPiProdMulFintypeProduct
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTsumCosetsFundamentalDomainEqCovol
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCongruenceLevelIffOrthEmbedding
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPointsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTransitiveAdelicUnitLengthVectors
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem real_quot {n m : ℕ} (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool) (x₀ : Fin n → ℂ)
    (B : Matrix (Fin n) (Fin m) ℂ) (j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε) (hn : m + 1 = n)
    (h1 : qEps ε x₀ = sgn ℝ s) (h2 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0)
    (h3 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε')
    (h4 : ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g) (c c' : ℝ) (hc : IsGauge ε c)
    (hc' : IsGauge ε' c') (b : Formalism.REAL.UJ ε → ENNReal) (hb : Measurable b)
    (hb1 : ∀ g, ∫⁻ h, b (j h * g) ∂(Formalism.REAL.muG ε') = 1) :
    ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ x₀)) * b g ∂(Formalism.REAL.muG ε) =
      ENNReal.ofReal c' * ENNReal.ofReal (2 ^ n * gaussDens ε (sgn ℝ s)) := by
  subst hn
  obtain ⟨c₀, h0, -, hu⟩ := GlobalTheory.T.riemannianHaarGauge_exists_pos_unique m ε'
  have hpos : 0 < c' := hu c' hc' ▸ h0
  have hne : ENNReal.ofReal c' ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
  have hinv : (ENNReal.ofReal c')⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne
  have hmul : ENNReal.ofReal c' * (ENNReal.ofReal c')⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top
  have key := GlobalTheory.T.gauge_measure_quotient_unitaryJ_vector_stabiliser m ε ε' s x₀ B j h1 h2 h3 h4 c c' hc hc'
    (fun g => (ENNReal.ofReal c')⁻¹ * b g) (hb.const_mul _) (fun g => by
      rw [lintegral_const_mul' _ _ hinv, hb1, mul_one, hmul])
  rw [← key]
  simp_rw [mul_left_comm _ (ENNReal.ofReal c')⁻¹]
  rw [lintegral_const_mul' _ _ hinv, mul_left_comm _ (ENNReal.ofReal c')⁻¹, ← mul_assoc (ENNReal.ofReal c'),
    hmul, one_mul]

theorem exists_rat (I : AutInst) : ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ (Γ : Set I.GA).Countable ∧
    DiscreteTopology Γ := by
  obtain ⟨⟨Γ, hΓ⟩, hc, hf⟩ := _root_.GlobalTheory.RatDiscrete.subgroup_countable_discrete I
  obtain ⟨-, -, h3, h4⟩ := _root_.GlobalTheory.adelicStab_isCompact_isOpen I
  refine ⟨Γ, hΓ, hΓ ▸ hc, ?_⟩
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : I.GA)
  have hfin : ((fun γ : Γ => (γ : I.GA)) ⁻¹' C).Finite := by
    refine Set.Finite.subset (Set.Finite.preimage Subtype.val_injective.injOn (hf C hC)) ?_
    intro γ hγ
    exact ⟨hΓ ▸ γ.2, hγ⟩
  have hn : ((fun γ : Γ => (γ : I.GA)) ⁻¹' C) ∈ nhds (1 : Γ) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hC1
  exact discreteTopology_of_isOpen_singleton_one (isOpen_singleton_of_finite_mem_nhds _ hn hfin)

theorem gauge_pos {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  obtain ⟨c₀, h0, -, hu⟩ := GlobalTheory.T.riemannianHaarGauge_exists_pos_unique n ε
  exact hu c h ▸ h0

theorem haar_muA (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] :
    (I.muA μf).IsHaarMeasure ∧ (I.muA μf).IsMulRightInvariant := by
  obtain ⟨-, -, h3, h4⟩ := _root_.GlobalTheory.adelicStab_isCompact_isOpen I
  have := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  refine ⟨?_, ⟨(GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf).2.1⟩⟩
  unfold AutInst.muA
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  exact Measure.prod.instIsHaarMeasure _ _

theorem unfold_sib (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hp : IsPerp D s x A xf)
    (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (c' : InfinitePlace I.F → ℝ) (μf' : Measure D.inst.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure]
    (fund : Set I.GA) (hc : IsGaugeAll I c) (hc' : IsGaugeAll D.inst c') (hf : I.IsFundDom (I.muA μf) fund) :
    ENNReal.ofReal (∏ v, c v) * (∫⁻ g in fund, gaussSum I (sgn I.E s) g ∂(I.muA μf)) / μf I.Kset =
      gaugeVol D.inst c' μf' * ENNReal.ofReal (2 ^ (I.n * I.f) * ∏ v, gaussDens (I.ε v) (sgn ℝ s)) := by
  obtain ⟨hKc, hKo, i1, i2⟩ := _root_.GlobalTheory.adelicStab_isCompact_isOpen I
  obtain ⟨hKc', hKo', i1', i2'⟩ := _root_.GlobalTheory.adelicStab_isCompact_isOpen D.inst
  have i3 := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  have i3' := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints D.inst
  obtain ⟨i4, -⟩ := haar_muA I μf
  obtain ⟨i4', i5'⟩ := haar_muA D.inst μf'
  have i6' : μf'.IsMulRightInvariant := ⟨(GlobalTheory.T.adelicUnitaryHaar_bi_invariant D.inst μf').2.2.2.1⟩
  obtain ⟨jf, hjf, hrange⟩ := _root_.GlobalTheory.StabUnfold.exists_finEmb I D s x A xf hp
  have hloc := _root_.GlobalTheory.StabUnfold.isPerp_at_place I D s x A xf hp
  choose jv hjc hjv using fun v => _root_.GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal I.n D.n (I.ε v) (D.ε v) s _ _ hp.1 (hloc v).1 (hloc v).2.1
    (hloc v).2.2
  obtain ⟨hK, hKg⟩ := _root_.GlobalTheory.StabUnfold.mem_level_iff_of_isFinEmb I D s x A xf hp jf hjf
  have hjfc := _root_.GlobalTheory.StabUnfold.isClosedEmbedding_of_conj_Kg I D.inst jf xf hKg
  have hj : Topology.IsClosedEmbedding (embA D jv jf) :=
    (Topology.IsClosedEmbedding.piMap hjc).prodMap hjfc
  obtain ⟨Γ, hΓ, hΓc, -⟩ := exists_rat I
  obtain ⟨Γ', hΓ', -, hΓd⟩ := exists_rat D.inst
  have hS : ((Γ'.map (embA D jv jf) : Subgroup I.GA) : Set I.GA) = stabF I x := by
    rw [Subgroup.coe_map, hΓ']
    exact _root_.GlobalTheory.StabUnfold.image_rational_eq_stab I D s x A xf hp jv jf hjv hjf
  obtain ⟨hopen, hmv, hleft, hright, hreal⟩ := _root_.GlobalTheory.StabUnfold.gaussAt_meas_inv I x
  have hind : Measurable ({h : I.Gf | x ∈ lamX I (1, h)}.indicator (1 : I.Gf → ENNReal)) :=
    measurable_one.indicator hopen.measurableSet
  have hΦ : Measurable (gaussAt I x) := by
    unfold gaussAt
    exact (Finset.measurable_prod _ fun v _ => (hmv v).comp ((measurable_pi_apply v).comp measurable_fst)).mul
      (hind.comp measurable_snd)
  have hinv : ∀ h g, gaussAt I x (embA D jv jf h * g) = gaussAt I x g := by
    intro h g
    unfold gaussAt
    congr 1
    · refine Finset.prod_congr rfl fun v _ => ?_
      exact congrArg (fun y => ENNReal.ofReal (gauss y)) (hreal v _ (g.1 v) (hjv v (h.1 v)).1)
    · have := hleft (jf h.2) g.2 (hjf h.2).1
      rw [show (embA D jv jf h * g).2 = jf h.2 * g.2 from rfl]
      by_cases hg : x ∈ lamX I (1, g.2)
      · rw [Set.indicator_of_mem (show _ ∈ {h : I.Gf | x ∈ lamX I (1, h)} from this.2 hg),
          Set.indicator_of_mem (show _ ∈ {h : I.Gf | x ∈ lamX I (1, h)} from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ {h : I.Gf | x ∈ lamX I (1, h)} from fun h' => hg (this.1 h')),
          Set.indicator_of_notMem (show _ ∉ {h : I.Gf | x ∈ lamX I (1, h)} from hg)]
  obtain ⟨ι, hι, r, hr1, hr2, hr3⟩ := _root_.GlobalTheory.StabCosets.gaussSum_cosets I s x hp.2.1
  have hmem : ∀ γ, γ ∈ Γ ↔ γ ∈ I.GFset := fun γ => by rw [← hΓ]; rfl
  have hmemS : ∀ γ, γ ∈ Γ'.map (embA D jv jf) ↔ γ ∈ stabF I x := fun γ => by rw [← hS]; rfl
  have horb := _root_.GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol I.GA Γ (Γ'.map (embA D jv jf)) (I.muA μf) fund (gaussAt I x) ι r hΓc
    (fun γ h => (hmem γ).2 ((hmemS γ).1 h).1) (fun γ _ => (GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf).1 γ) hf.1
    (fun y => by obtain ⟨γ, h1, h2⟩ := hf.2.1 y; exact ⟨γ, (hmem γ).2 h1, h2⟩)
    (fun γ h => hf.2.2 γ ((hmem γ).1 h)) hΦ
    (by rintro _ ⟨h, -, rfl⟩ g; exact hinv h g) (fun i => (hmem _).2 (hr1 i))
    (fun γ h => by simp only [hmemS]; exact hr2 γ ((hmem γ).1 h))
  have i7 : ∀ v, (Formalism.REAL.muG (D.ε v)).IsMulRightInvariant := fun v => ⟨Formalism.REAL.indefinite_unitary_unimodular _ _⟩
  choose bv hbv hbv1 using fun v => _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one _ _ (Formalism.REAL.muG (D.ε v)) (jv v) (hjc v)
  obtain ⟨bf, hbf, hbf1, hbf2⟩ := _root_.GlobalTheory.StabUnfold.exists_cutoff_doubleCoset I.Gf D.inst.Gf μf μf' jf hjfc (Ksub I) (Ksub D.inst) xf
    {h : I.Gf | x ∈ lamX I (1, h)} hKo hKo' hKc' hK (fun g => by
      constructor
      · intro hg
        obtain ⟨h, h1, k, hk, e⟩ := _root_.GlobalTheory.FinOrbit.exists_stab_mul_level I s x xf g hp.2.1 hp.2.2.2.2.1 hg
        obtain ⟨h', rfl⟩ := hrange h h1
        exact ⟨h', k, hk, e⟩
      · rintro ⟨h, k, hk, rfl⟩
        exact (hright _ k hk).2 ((hleft _ _ (hjf h).1).2 hp.2.2.2.2.1))
  have hb : Measurable fun g : I.GA => (∏ v, bv v (g.1 v)) * bf g.2 :=
    (Finset.measurable_prod _ fun v _ => (hbv v).comp ((measurable_pi_apply v).comp measurable_fst)).mul
      (hbf.comp measurable_snd)
  have hb1 : ∀ g : I.GA, ∫⁻ h, (∏ v, bv v ((embA D jv jf h * g).1 v)) * bf (embA D jv jf h * g).2
      ∂(D.inst.muA μf') = 1 := by
    intro g
    have := _root_.GlobalTheory.StabUnfold.lintegral_pi_prod_mul _ _ (fun v => Formalism.REAL.muG (D.ε v)) _ μf' (fun v h => bv v (jv v h * g.1 v))
      (fun h => bf (jf h * g.2))
      (fun v => (hbv v).comp (((hjc v).continuous.mul continuous_const).measurable))
      (hbf.comp ((hjfc.continuous.mul continuous_const).measurable))
    simp only [hbv1, hbf1, Finset.prod_const_one, mul_one] at this
    exact this
  have hun := _root_.GlobalTheory.GenUnfold.covol_withDensity_eq I.GA D.inst.GA (I.muA μf) (D.inst.muA μf') (embA D jv jf) hj Γ' (gaussAt I x) _ hΦ hb
    hinv hb1
  have hint : ∫⁻ g, gaussAt I x g * ((∏ v, bv v (g.1 v)) * bf g.2) ∂(I.muA μf) =
      (∏ v, ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) * bv v g ∂(Formalism.REAL.muG (I.ε v))) *
        (μf I.Kset / μf' D.inst.Kset) := by
    have := _root_.GlobalTheory.StabUnfold.lintegral_pi_prod_mul _ _ (fun v => Formalism.REAL.muG (I.ε v)) _ μf
      (fun v g => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) * bv v g)
      (fun g => {h : I.Gf | x ∈ lamX I (1, h)}.indicator 1 g * bf g)
      (fun v => (hmv v).mul (hbv v)) (hind.mul hbf)
    rw [hbf2] at this
    refine Eq.trans (lintegral_congr fun g => ?_) this
    unfold gaussAt
    rw [Finset.prod_mul_distrib, mul_mul_mul_comm]
  have hq := fun v => real_quot (I.ε v) (D.ε v) s _ _ (jv v) hp.1 (hloc v).1 (hloc v).2.1 (hloc v).2.2 (hjv v)
    (c v) (c' v) (hc v) (hc' v) (bv v) (hbv v) (hbv1 v)
  have hs : sgn ℝ s ≠ 0 := by unfold sgn; split_ifs <;> norm_num
  have hd : ∀ v, 0 ≤ gaussDens (I.ε v) (sgn ℝ s) := fun v => ((GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous _ (I.ε v)).1 _ hs).2
  have hprod := Finset.prod_congr (s₁ := Finset.univ) rfl fun v _ => hq v
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => (gauge_pos (hc v)).le,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => (gauge_pos (hc' v)).le,
    ← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (by positivity) (hd v), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, (GlobalTheory.T.autInst_degree_rootDiscriminant_rank I).2.2.2.2.1, ← pow_mul] at hprod
  have hK0 : μf I.Kset ≠ 0 := (hKo.measure_pos μf ⟨1, (Ksub I).one_mem⟩).ne'
  have hKt : μf I.Kset ≠ ⊤ := hKc.measure_lt_top.ne
  simp_rw [hr3]
  rw [horb, hun, hint, hΓ', gaugeVol, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  generalize covol D.inst.GFset (D.inst.muA μf') Set.univ = a
  generalize (μf' D.inst.Kset)⁻¹ = t
  have h1 := ENNReal.mul_inv_cancel hK0 hKt
  calc _ = a * t * (ENNReal.ofReal (∏ v, c v) * ∏ v, ∫⁻ g, ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x)) *
        bv v g ∂(Formalism.REAL.muG (I.ε v))) * (μf I.Kset * (μf I.Kset)⁻¹) := by ring
    _ = _ := by rw [hprod, h1]; ring

theorem gaugeUnfold : GaugeUnfold := by
  intro I I' e s x A xf _ hp c μf _ _ c' μf' _ _ fund hc hc' hf
  obtain ⟨D, B, hD, hvol⟩ := _root_.GlobalTheory.PerpReduce.exists_sib I I' e s x A xf hp
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_sigmaFinite_haar_finiteAdelicUnitary D.inst
  choose d _ hd _ using fun v => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique D.n (D.ε v)
  rw [← hvol d μ c' μf' hd hc']
  exact unfold_sib I D s x B xf hD c μf d μ fund hc hd hf

end GlobalTheory.StabUnfold
