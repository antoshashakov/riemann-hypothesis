module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJInvariantInModularFunctionFractionField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExistsGammaLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldIsAlgebraicAdjoinJInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOneStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldAnSlGerm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominators
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldConstAndQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpansionConverges
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonempty
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightActionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem tower_exists : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  intro Ω _ _ _ ε
  obtain ⟨T⟩ := _root_.GlobalTheory.FN.frac_nonempty Ω ε
  obtain ⟨a, ha, hinv, h1, h2, h3⟩ := _root_.GlobalTheory.FN.j_in_frac Ω ε T
  have hgerm := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hj := GlobalTheory.T.lv_jT_one_and_jT_smul_eq
  have hhol : DifferentiableOn ℂ (up jT) Hs :=
    (hgerm.2.1 jT).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ⊤ jT ⟨1, 1, one_pos, (hj ⊤).1⟩)
  refine ⟨{ K := T.K, exp := T.exp, sl := T.sl, sl_one := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).1, sl_mul := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).2,
            gal := T.gal, gal_exp := T.gal_exp,
            an := T.an, an_c := (_root_.GlobalTheory.FN.frac_const_and_quot Ω ε T).1, an_sl := _root_.GlobalTheory.FN.an_sl_germ Ω ε T, an_mero := (_root_.GlobalTheory.FN.frac_const_and_quot Ω ε T).2,
            an_exp := fun f => (_root_.GlobalTheory.FN.frac_exp_converges Ω ε T f).2,
            level := _root_.GlobalTheory.FN.frac_exists_level Ω ε T, exp_upper := _root_.GlobalTheory.FN.exp_sl_coeff_upper Ω ε T, recip := _root_.GlobalTheory.FNRecip.main Ω ε T,
            jK := T.io a, j_inv := hinv, j_exp := ⟨h1, h2, h3⟩,
            j_hol := ⟨up jT, by rw [T.an_io, ha]; rfl, hhol⟩,
            alg_j := _root_.GlobalTheory.FN.frac_isAlgebraic_adjoin_j Ω ε T a ha, bdd := _root_.GlobalTheory.FN.frac_bdd_den Ω ε T, sat := _root_.GlobalTheory.fn_sat Ω ε T,
            mem_q := _root_.GlobalTheory.FN.exists_of_qexp Ω ε T }, ?_⟩
  show T.an (T.io a) = germ jT
  rw [T.an_io, ha]

end GlobalTheory.FN
