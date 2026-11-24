module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPowFinrankEqSpanDiscr
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' : ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  first | exact @GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | exact GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | (intros; apply GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr <;> assumption)
