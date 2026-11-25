module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TemperedProductOfSquareIntegrable
public import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WindowBoundOfLiteratureLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
theorem UpperTheory.One.Join.local_inputs_from_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition) :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt :=
  { bz := (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_finiteness_of_open O)
    bern := (_root_.UpperTheory.LiteratureTheorems.bernstein_unitary_product_irreducible_of_open O)
    geo := (_root_.UpperTheory.LiteratureTheorems.bernstein_zelevinsky_geometric_of_open O)
    zel := (_root_.UpperTheory.LiteratureTheorems.zelevinsky_polynomial_ring_of_open O)
    disj := (_root_.UpperTheory.LiteratureTheorems.totally_disjoint_product_irreducible_of_open O)
    mp := (_root_.UpperTheory.LiteratureTheorems.moy_prasad_jacquet_iso_of_open O)
    temp := (_root_.UpperTheory.LiteratureTheorems.tempered_product_of_square_integrable_of_open O)
    seg := (_root_.UpperTheory.LiteratureTheorems.ess_square_integrable_segments_of_open O)
    sq := (_root_.UpperTheory.LiteratureTheorems.square_integrable_segment_of_open O)
    gen := (_root_.UpperTheory.LiteratureTheorems.generic_unlinked_gl_of_open O)
    multi := (_root_.UpperTheory.LiteratureTheorems.langlands_multisegments_of_open O)
    exh := (_root_.UpperTheory.LiteratureTheorems.langlands_exhaustion_gl_of_open O)
    cos := (_root_.UpperTheory.LiteratureTheorems.standard_cosocle_gl_of_open O)
    conv := (_root_.UpperTheory.LiteratureTheorems.local_converse_gl_of_open O)
    dzi := (_root_.UpperTheory.LiteratureTheorems.depth_zero_induction_of_open O)
    brauer := (_root_.UpperTheory.LiteratureTheorems.brauer_degree_zero_of_open O)
    chev := (_root_.UpperTheory.LiteratureTheorems.chevalley_units_of_open O)
    green := (_root_.UpperTheory.LiteratureTheorems.green_regular_characters_of_open O) }
theorem UpperTheory.One.Join.automorphic_inputs_from_literature (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition) (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN)
    (gal : _root_.UpperTheory.V.Z.Win.RowT) : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureAutomorphyHypothesis :=
  { decay := (_root_.UpperTheory.LiteratureTheorems.cusp_rapid_decay_of_open O)
    hc := (_root_.UpperTheory.LiteratureTheorems.harish_chandra_finite_of_open O)
    fin := (_root_.UpperTheory.LiteratureTheorems.automorphic_forms_finite_gl_of_open O)
    js := (_root_.UpperTheory.LiteratureTheorems.jacquet_shalika_of_open O)
    cusp := (_root_.UpperTheory.LiteratureTheorems.cuspidal_spectrum_gl_of_open O)
    bc := bc
    gk := (_root_.UpperTheory.LiteratureTheorems.gelfand_kazhdan_dual_of_open O)
    gal := gal
    pur := (_root_.UpperTheory.LiteratureTheorems.clozel_purity_of_open O)
    coh := (_root_.UpperTheory.LiteratureTheorems.clozel_cohomological_of_open O)
    art := (_root_.UpperTheory.LiteratureTheorems.global_artin_reciprocity_of_open O)
    ray := (_root_.UpperTheory.LiteratureTheorems.ray_class_field_st_of_open O)
    chA := (_root_.UpperTheory.LiteratureTheorems.hecke_ladic_character_above_of_open O)
    chW := (_root_.UpperTheory.LiteratureTheorems.algebraic_character_wd_of_open O)
    berger := (_root_.UpperTheory.LiteratureTheorems.de_rham_pot_semistable_of_open O) }
theorem UpperTheory.One.Join.v_window_of_depth_zero_residual_bc_cm (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition)
 (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN) (gal : _root_.UpperTheory.V.Z.Win.RowT) :
    UpperTheory.Top.VWin :=
  _root_.UpperTheory.V.v_window_of_literal_automorphy_n
    { loc := _root_.UpperTheory.One.Join.local_inputs_from_literature O
      aut := _root_.UpperTheory.One.Join.automorphic_inputs_from_literature O bc gal
      coh := _root_.UpperTheory.LiteratureTheorems.galois_cohomology_from_literature O }
theorem UpperTheory.One.Join.automorphic_window_of_inputs (O : _root_.UpperTheory.LiteratureTheorems.OpenImageCondition)
 (bc : _root_.PositivityTheory.Rg.BcN.BaseChangeIsobaricN) (gal : _root_.UpperTheory.V.Z.Win.RowT) :
    UpperTheory.Top.VWin :=
  _root_.UpperTheory.One.Join.v_window_of_depth_zero_residual_bc_cm O bc gal
end
