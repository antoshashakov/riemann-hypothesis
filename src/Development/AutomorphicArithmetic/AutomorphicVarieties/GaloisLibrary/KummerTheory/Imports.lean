module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HilbertNinety
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.h90 :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (f : G K Ω → Ω), IsLocallyConstant f → (∀ g, f g ≠ 0) → (∀ g h, f (g * h) = f g * g (f h)) → ∃ β : Ω, β ≠ 0 ∧ ∀ g : G K Ω, g β = f g * β :=
  _root_.UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90
