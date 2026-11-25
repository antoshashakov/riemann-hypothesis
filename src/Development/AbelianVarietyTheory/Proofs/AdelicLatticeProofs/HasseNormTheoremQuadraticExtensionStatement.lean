module

public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.hasse_norm_theorem_quadratic_extension : GlobalTheory.Published.HasseNormSt := by
  first | exact @GlobalTheory.QNorm.hasseNormSt | exact GlobalTheory.QNorm.hasseNormSt | (intros; apply GlobalTheory.QNorm.hasseNormSt <;> assumption)
