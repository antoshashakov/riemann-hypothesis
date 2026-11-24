module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomologyStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixingStatement
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem NS_eq_fixingSubgroup (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
  le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (GlobalTheory.T.galois_unramified_outside_cohomology F Ω S)

end GlobalTheory.CompanionTheory.Hypotheses₂
