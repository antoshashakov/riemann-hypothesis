module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]



def genMap (P : Ideal (MRing ι)) {N1 : ℕ} {S : Type} [Fintype S] (v : S → Fin N1 → FnField P) :
    MRing (PBlk ι N1) →+* MvPolynomial S (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr _, j⟩ => ∑ s, C (v s j) * X s



end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
