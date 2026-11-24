module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionMatchedPartsDimEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaRecognition_matched_parts_dim_eq : AllMatch fun μ g g' => μ.A ∧ g = g' := by
  first | exact @GlobalTheory.MatchParts.match_parts | exact GlobalTheory.MatchParts.match_parts | (intros; apply GlobalTheory.MatchParts.match_parts <;> assumption)
