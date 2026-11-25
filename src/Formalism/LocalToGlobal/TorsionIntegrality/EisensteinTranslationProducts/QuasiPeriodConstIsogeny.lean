module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.FormEvenIff
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.L2.Th1.F

theorem quasiPeriodConstIsogeny : QuasiPeriodConstIsogeny := quasiPeriodConstIsogeny_thm
theorem cmTheta0 : CmTheta0 := cm_even_theta

end Formalism.L2.Th1.F
