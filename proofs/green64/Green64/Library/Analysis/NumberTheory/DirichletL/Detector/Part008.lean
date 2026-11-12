module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part002
public import Green64.Library.OAI.NumberTheory.DirichletL.Detector.GramPeriodicPoisson
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part003

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.GramJointPeriod -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma common_radical_norm_le (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (∏i,P i)≤Ideal.absNorm (Ideal.span {C}) := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hC)))
  apply map_dvd Ideal.absNorm
  rw [he]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))

lemma jointPeriod_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (jointPeriod S hS P r)≤
      Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) := by
  rw [jointPeriod,map_mul,map_mul]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (common_radical_norm_le C hC P c hc he))
    (numerator_good_norm_le u a b r k hk hk0)

lemma jointPeriod_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (he : Ideal.span {C}=∏i,P i^c i) (r : O) (hr : r≠0) :
    jointPeriod S hS P r≠0 := by
  have hp : ∏i,P i≠(0:Id) := by
    intro hz
    have hd : (∏i,P i)∣Ideal.span {C} := by
      rw [he]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))
    rw [hz,zero_dvd_iff] at hd
    exact hC (Ideal.span_singleton_eq_bot.mp hd)
  exact mul_ne_zero (mul_ne_zero (jointFixedModulus_nonzero S hS) hp)
    (Ideal.span_singleton_eq_bot.not.mpr hr)

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramMobiusPool -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma divisorPool_supported (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    Supported D := by
  obtain ⟨J,hJ,hd⟩ := Finset.mem_biUnion.mp hD
  exact gram_supported_divisor J.val D J.property ((mem_idealDivisors J.property.1).mp hd)

def poolDivisor (G : Finset SupportedIdeal) (D : Id) : SupportedIdeal :=
  if hD : D∈divisorPool G Subtype.val then ⟨D,divisorPool_supported G D hD⟩
  else ⟨1,by
    constructor
    · exact one_ne_zero
    · intro P hP
      change P∈normalizedFactors (1:Id) at hP
      rw [normalizedFactors_one] at hP
      simp at hP⟩

lemma poolDivisor_val (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    (poolDivisor G D).val=D := by simp [poolDivisor,hD]

lemma finite_pair_eq_tsum (F G : Finset SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ)
    (hf : ∀I J,I∉F ∨ J∉G→f I J=0) :
    (∑I∈F,∑J∈G,f I J)=∑'I : SupportedIdeal,∑'J : SupportedIdeal,f I J := by
  have hinner (I : SupportedIdeal) : (∑J∈G,f I J)=∑'J : SupportedIdeal,f I J :=
    (tsum_eq_sum (fun J hJ=>hf I J (Or.inr hJ))).symm
  simp_rw [hinner]
  symm
  apply tsum_eq_sum
  intro I hI
  simp only [hf I _ (Or.inl hI),tsum_zero]

theorem finite_pair_mobius_dilation (F G : Finset SupportedIdeal)
    (f : SupportedIdeal→SupportedIdeal→ℂ) (hf : ∀I J,I∉F ∨ J∉G→f I J=0) :
    (∑I∈F,∑J∈G,if IsCoprime I.val J.val then f I J else 0)=
      ∑D∈divisorPool G Subtype.val,(moebius D:ℂ)*
        ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
          f (supportedIdealProduct (poolDivisor G D) I) (supportedIdealProduct (poolDivisor G D) J) := by
  rw [finite_pair_mobius F G Subtype.val Subtype.val (fun J _=>J.property.1) f]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hd := poolDivisor_val G D hD
  rw [finite_pair_eq_tsum F G (fun I J=>if D∣I.val ∧ D∣J.val then f I J else 0) (by
    intro I J h
    simp only [hf I J h,ite_self])]
  convert supported_divisor_pair_tsum (poolDivisor G D) f using 1
  rw [hd]

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramPrimeSeparation -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma maximal_coprime_of_not_dvd (p J : Id) [p.IsMaximal] (h : ¬p∣J) : IsCoprime J p := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  have he : p=J⊔p := Ideal.IsMaximal.eq_of_le inferInstance htop le_sup_right
  apply h
  apply Ideal.dvd_iff_le.mpr
  rw [he]
  exact le_sup_left

theorem exists_prime_separation (I p : Id) (hI : I≠0) [p.IsMaximal] (hp0 : p≠0) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧ IsCoprime J p ∧ J≠0 := by
  have hp : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  obtain ⟨J,hJ,hnd⟩ := (FiniteMultiplicity.of_prime_left hp hI).exists_eq_pow_mul_and_not_dvd
  have he : multiplicity p I=(normalizedFactors I).count p := by
    simpa only [normalize_eq] using multiplicity_eq_count_normalizedFactors hp.irreducible hI
  refine ⟨J,?_,maximal_coprime_of_not_dvd p J hnd,?_⟩
  · rw [←he,mul_comm]
    exact hJ
  · intro hz
    rw [hz,mul_zero] at hJ
    exact hI hJ

theorem exists_nonexceptional_separation (L R I p : Id) (hI : I≠0)
    [p.IsMaximal] (hp0 : p≠0) (hL : ¬p∣L) (hR : ¬p∣R) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧
      IsCoprime (L*R*J) (p^((normalizedFactors I).count p)) ∧ J≠0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_prime_separation I p hI hp0
  exact ⟨J,hJ,((maximal_coprime_of_not_dvd p L hL).mul_left
    (maximal_coprime_of_not_dvd p R hR)).mul_left hcop |>.pow_right,hJ0⟩

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramResidue -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem exists_nonexceptional_residue (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : Supported (Ideal.span {r})) (hk : k=u.val*goodLambda^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hfac : Ideal.span {C}=∏i,P i^c i)
    (p : Id) [p.IsMaximal] (hp0 : p≠0) (hgp : goodLambda∉p)
    (hchar : ringChar (O⧸p)≠2) (hfixed : ¬p∣jointFixedModulus S hS) (hcommon : ¬p∣∏i,P i)
    (he : ¬6∣(normalizedFactors (Ideal.span {r})).count p) :
    ∃(M : Id)(hM : M≠0),
      Ideal.absNorm M≤Ideal.absNorm (jointFixedModulus S hS)*
        Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) ∧
      letI : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient hM
      letI : Fintype (O⧸M):=Fintype.ofFinite _
      ∀d : O,∃A : (O⧸M)→(O⧸M)→ℂ,
        (∀n₁ n₂,A (Ideal.Quotient.mk M n₁) (Ideal.Quotient.mk M n₂)=
          jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)) ∧
        (∀x y,‖A x y‖≤Ideal.absNorm (Ideal.span {C})) ∧
        (∑x,∑y,A x y)=0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_nonexceptional_separation (jointFixedModulus S hS)
    (∏i,P i) (Ideal.span {r}) p hr.1 hp0 hfixed hcommon
  let e := (normalizedFactors (Ideal.span {r})).count p
  let M : Id := (jointFixedModulus S hS*(∏i,P i)*J)*p^e
  have hMperiod : M=jointPeriod S hS P r := by
    rw [jointPeriod,hJ]
    dsimp [M,e]
    ring
  have hM0 : M≠0 := hMperiod ▸ jointPeriod_nonzero S hS C hC P c hc hfac r
    (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)
  refine ⟨M,hM0,?_,?_⟩
  · rw [hMperiod]
    exact jointPeriod_norm_bound S hS C k hC hk0 u a b r hk P c hc hfac
  · let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM0
    let : Fintype (O⧸M) := Fintype.ofFinite _
    let : Finite (O⧸jointFixedModulus S hS*(∏i,P i)*J) :=
      Ring.HasFiniteQuotients.finiteQuotient (left_ne_zero_of_mul hM0)
    let : Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J) := Fintype.ofFinite _
    let : Finite (O⧸p^e) := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ hp0)
    let : Fintype (O⧸p^e) := Fintype.ofFinite _
    intro d
    let A : (O⧸M)→(O⧸M)→ℂ := fun x y=>
      jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out)
    refine ⟨A,?_,?_,?_⟩
    · intro n₁ n₂
      apply jointExtension_dilation_periodic
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₁))
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₂))
    · intro x y
      rw [hfac]
      exact jointExtension_norm S hS σ C k u a b r hr P hg c hc _ _
    · exact jointExtension_mean_zero S hS σ C k u a b r hr P hg c J p hgp hchar e he hJ hcop d

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramNonexceptionalBlock -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "Joint" => ProbeGramPeriodicPoisson.Joint

theorem literal_nonexceptional_block (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃H : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤ c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(W : SchwartzMap Joint ℂ),ProbeGramAnnularLattice.AnnularSupport a₀ b₀ W→
      ∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)‖≤
        K*ProbeGramLatticeDecay.sourceControl H W*(Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H,K,hK,hengine⟩ := ProbeGramPeriodicPoisson.ideal_annular_periodic_bound A hA a₀ b₀ ha₀ hab
  refine ⟨H,K,hK,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he W hW d N hN
  have hcount : (normalizedFactors (Ideal.span {k})).count p=
      (normalizedFactors (Ideal.span {r})).count p := by
    rw [hk]
    exact good_factor_count p hgp hchar u a b r hr
  have heR : ¬6∣(normalizedFactors (Ideal.span {r})).count p := hcount ▸ he
  obtain ⟨M,hM,hMN,hres⟩ := exists_nonexceptional_residue S hS σ C k hC hk0 u a b r hr hk
    P hg c hc hfac p hp0 hgp hchar hfixed hcommon heR
  let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype (O⧸M) := Fintype.ofFinite _
  obtain ⟨f,hf,hfn,hfm⟩ := hres d
  have hmean : (∑'v : (O⧸M)×(O⧸M),f v.1 v.2)=0 := by
    rw [tsum_fintype,Fintype.sum_prod_type]
    exact hfm
  have hh := hengine W hW M hM (fun v=>f v.1 v.2) (Ideal.absNorm (Ideal.span {C}))
    (Nat.cast_nonneg _) (fun v=>hfn v.1 v.2) hmean N hN
  have hfun : (fun m : O×O=>f (ProbeGramPeriodicPoisson.idealQuotientPair M m).1
      (ProbeGramPeriodicPoisson.idealQuotientPair M m).2*W (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) := by
    funext m
    rw [ProbeGramPeriodicPoisson.idealQuotientPair,hf]
  rw [hfun] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold ProbeGramLatticeDecay.sourceControl;positivity)
  apply min_le_min_left
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ hN.le
  exact_mod_cast hMN

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowGramHeight -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap Topology
open Filter Set CompletedHeight FourierBridge
namespace SevenEighths.ProbePhysical

def lowGramBaseWindow (W : ℝ→ℂ) (r : ℝ) : ℂ := W r/(r:ℂ)

lemma lowGramBaseWindow_support (W : ℝ→ℂ) :
    Function.support (lowGramBaseWindow W)⊆Function.support W := by
  intro r hr hz
  exact hr (by simp [lowGramBaseWindow,hz])

lemma lowGramBaseWindow_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (lowGramBaseWindow W) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r=0
  · subst r
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ=>(0:ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ha] with x hx
    have hz : W x=0 := by
      by_contra h
      exact (not_le.mpr hx) (hs h).1
    simp [lowGramBaseWindow,hz]
  · unfold lowGramBaseWindow
    simp only [div_eq_mul_inv]
    exact hW.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.fun_inv (Complex.ofReal_ne_zero.mpr hr))

lemma lowGramProfile_twist (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (v r : ℝ) :
    lowGramProfile W v r=normTwistedSource (lowGramBaseWindow W) (v/(2*Real.pi)) r := by
  by_cases hz : W r=0
  · simp [lowGramProfile,normTwistedSource,lowGramBaseWindow,hz]
  have hr : 0< r := ha.trans_le (hs hz).1
  have hrc : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hp : (r:ℂ)^((v:ℂ)*Complex.I)=logPhase (v/(2*Real.pi)) (Real.log r) := by
    rw [Complex.cpow_def_of_ne_zero hrc,←Complex.ofReal_log hr.le]
    unfold logPhase
    congr 1
    push_cast
    field_simp
  rw [lowGramProfile,Complex.cpow_add _ _ hrc,Complex.cpow_neg_one,hp]
  unfold normTwistedSource lowGramBaseWindow
  ring

def lowGramSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) : SchwartzMap ℝ ℂ :=
  uniformTwistedSchwartz (lowGramBaseWindow W) a b ha
    ((lowGramBaseWindow_support W).trans hs) (lowGramBaseWindow_smooth W a b ha hs hW) (v/(2*Real.pi))

lemma lowGramSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v r : ℝ) :
    lowGramSchwartz W a b ha hs hW v r=lowGramProfile W v r := by
  rw [lowGramSchwartz,uniformTwistedSchwartz_apply,lowGramProfile_twist W a b ha hs]

theorem lowGramProfile_uniform_degree (a b : ℝ) (ha : 0<a) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∀W : ℝ→ℂ,∀hs : Function.support W⊆Set.Icc a b,∀hW : ContDiff ℝ ∞ W,
      ∃C : ℝ,0<C ∧ ∀v : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (lowGramSchwartz W a b ha hs hW v)≤C*(1+‖v‖)^n := by
  obtain ⟨n,hn⟩ := normTwistedSource_uniform_degree a b ha S
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn (lowGramBaseWindow W) ((lowGramBaseWindow_support W).trans hs)
    (lowGramBaseWindow_smooth W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro v
  apply (hb (v/(2*Real.pi))).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  gcongr
  simp only [norm_div,Real.norm_eq_abs,abs_of_pos (show (0:ℝ)<2*Real.pi by positivity)]
  exact div_le_self (norm_nonneg v) (by linarith [Real.pi_gt_three])

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramShell -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical EisensteinSchwartzPoisson

def shellProfile (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ) : ℂ :=
  lowGramProfile W v x*star (lowGramProfile W v y)*paperRadialFourier U (T/(x*y))

lemma shellProfile_zero_left (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hx : W x=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hx]

lemma shellProfile_zero_right (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hy : W y=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hy]

theorem shellProfile_weighted_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
      ∀(W : ℝ→ℂ),(Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤B)→
      ∀(U : SchwartzMap ℝ ℂ)(v T x y : ℝ),0≤T→
        (1+T)^A*‖shellProfile W v U T x y‖≤
          C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := by
  obtain ⟨s,C,hC,hpaper⟩ := paperRadialFourier_euler_source_weighted_bound A 0
  refine ⟨s,(1+B/a)^2*(1+b^2)^A*C,by positivity,?_⟩
  intro W hs hW U v T x y hT
  by_cases hx : W x=0
  · rw [shellProfile_zero_left _ _ _ _ _ _ hx,norm_zero,mul_zero]
    positivity
  by_cases hy : W y=0
  · rw [shellProfile_zero_right _ _ _ _ _ _ hy,norm_zero,mul_zero]
    positivity
  have hxa := (hs hx).1
  have hya := (hs hy).1
  have hxb := (hs hx).2
  have hyb := (hs hy).2
  have hx0 := ha.trans_le hxa
  have hy0 := ha.trans_le hya
  have hxy : 0<x*y := mul_pos hx0 hy0
  have hxyb : x*y≤b^2 := by nlinarith [mul_le_mul hxb hyb hy0.le (hx0.le.trans hxb)]
  have ht : 0≤T/(x*y) := div_nonneg hT hxy.le
  have hp := hpaper U 0 (by omega) (T/(x*y)) ht
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hp
  have hscale : 1+T≤(1+b^2)*(1+T/(x*y)) := by
    have he : T=(x*y)*(T/(x*y)) := by field_simp
    have hbound := mul_le_mul_of_nonneg_right hxyb ht
    rw [←he] at hbound
    nlinarith [sq_nonneg b]
  have hp' : (1+T)^A*‖paperRadialFourier U (T/(x*y))‖≤
      (1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    calc
      _ ≤ ((1+b^2)*(1+T/(x*y)))^A*‖paperRadialFourier U (T/(x*y))‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale _) (norm_nonneg _)
      _ = (1+b^2)^A*((1+T/(x*y))^A*‖paperRadialFourier U (T/(x*y))‖) := by rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hwx : ‖lowGramProfile W v x‖≤1+B/a := by
    rw [lowGramProfile_norm W v x hx0]
    exact (div_le_div₀ hB (hW x) ha hxa).trans (by linarith)
  have hwy : ‖lowGramProfile W v y‖≤1+B/a := by
    rw [lowGramProfile_norm W v y hy0]
    exact (div_le_div₀ hB (hW y) ha hya).trans (by linarith)
  rw [shellProfile,norm_mul,norm_mul,norm_star]
  calc
    _ = (‖lowGramProfile W v x‖*‖lowGramProfile W v y‖)*
        ((1+T)^A*‖paperRadialFourier U (T/(x*y))‖) := by ring
    _ ≤ (1+B/a)^2*((1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul _ hp' (by positivity) (by positivity)
      nlinarith [mul_le_mul hwx hwy (norm_nonneg _) (by positivity : 0≤1+B/a)]
    _ = _ := by ring

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramAnnularCount -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma nonzero_norm_one_le (z : O) (hz : z≠0) : (1:ℝ)≤‖eisEmbedding z‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hz))

theorem annular_element_count (F : Finset O) (b N : ℝ) (hb : 0≤b) (hN : 0≤N)
    (hzero : ∀z∈F,z≠0) (hbound : ∀z∈F,‖eisEmbedding z‖^2≤b*N) :
    (F.card:ℝ)≤128*b*N := by
  by_cases hF : F.Nonempty
  · obtain ⟨z,hz⟩ := hF
    have hscale : 1≤b*N := (nonzero_norm_one_le z (hzero z hz)).trans (hbound z hz)
    simpa only [mul_assoc] using DescentFiberCost.finite_element_count_real F (b*N) hscale hbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF,Finset.card_empty,Nat.cast_zero]
    positivity

theorem annular_pair_count (F G : Finset O) (b N : ℝ) (hb : 0≤b) (hN : 0≤N)
    (hFzero : ∀z∈F,z≠0) (hGzero : ∀z∈G,z≠0)
    (hFbound : ∀z∈F,‖eisEmbedding z‖^2≤b*N)
    (hGbound : ∀z∈G,‖eisEmbedding z‖^2≤b*N) :
    ((F×ˢG).card:ℝ)≤(128*b)^2*N^2 := by
  rw [Finset.card_product,Nat.cast_mul]
  have hf := annular_element_count F b N hb hN hFzero hFbound
  have hg := annular_element_count G b N hb hN hGzero hGbound
  calc
    _ ≤ (128*b*N)*(128*b*N) := mul_le_mul hf hg (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramLatticeWindow -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def shellLatticeColumns (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) : Finset O :=
  (elementWindow_finite_support W hW N hN).toFinset

lemma shellLatticeColumns_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) (n : O) :
    n∈shellLatticeColumns W hW N hN ↔ W (‖eisEmbedding n‖^2/N)≠0 := by
  simp only [shellLatticeColumns,Set.Finite.mem_toFinset,Function.mem_support]
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rfl

lemma shellLatticeColumns_nonzero (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : n≠0 := by
  intro hz
  have hh := (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).1
  simp only [hz,map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div] at hh
  linarith

lemma shellLatticeColumns_norm (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : ‖eisEmbedding n‖^2≤b*N :=
  (div_le_iff₀ hN).mp (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).2

lemma shell_lattice_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (n m : O)
    (h : n∉shellLatticeColumns W hW N hN ∨ m∉shellLatticeColumns W hW N hN) :
    shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [shellLatticeColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [shellLatticeColumns_mem,not_not] using h

lemma shell_lattice_summable (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    Summable (fun m : O×O=>f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
  apply summable_of_ne_finset_zero (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN))
  intro m hm
  have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
  rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero]

lemma shell_lattice_tsum (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    (∑'m : O×O,f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N))=
      ∑n∈shellLatticeColumns W hW N hN,∑m∈shellLatticeColumns W hW N hN,
        f n m*shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N) := by
  rw [tsum_eq_sum (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN)) (by
    intro m hm
    have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
    rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero])]
  exact Finset.sum_product _ _ _

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowGramPoisson -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowGram_pair_prefactor (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v Q : ℝ) (s t : {I : Id // Supported I}) :
    (lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
      ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)))=
      ((Q/Y^3:ℝ):ℂ)*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
  calc
    _ = (Q:ℂ)*(lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ))*
        star (lowGaussColumn C W1 Y σ v t/(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)) := by
      simp only [Complex.star_def,map_mul,map_inv₀,Complex.conj_ofReal,div_eq_mul_inv,mul_inv_rev]
      ring
    _ = (Q:ℂ)*(lowGramScale Y*star (lowGramScale Y))*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
      rw [lowGaussColumn_unnormalized C W1 Y hY σ v s,lowGaussColumn_unnormalized C W1 Y hY σ v t]
      simp only [star_mul]
      ring
    _ = _ := by rw [lowGramScale_mul_star Y hY];simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]

theorem lowGram_source_poisson (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    gaussEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
      (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
      (lowGaussColumn C W1 Y σ v) U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          ∑'h : O,actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val)
            ((supported_span_primaryGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryGenerator_iff t.val).mpr t.property) (-h)*
            paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2) := by
  rw [gaussEnergy_poisson _ _ _ _ U Q hQ]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1)
  rw [hes,het,←mul_assoc,lowGram_pair_prefactor C W1 Y hY σ v Q s t,mul_assoc]

theorem lowGram_kernel_scale (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (s t : {I : Id // Supported I}) (h : O) :
    Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2=
      ‖eisEmbedding h‖^2/((Y^2/Q)*((Ideal.absNorm s.val:ℝ)/Y)*((Ideal.absNorm t.val:ℝ)/Y)) := by
  simp_rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rw [←Ideal.span_singleton_mul_span_singleton]
  rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1,
    (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1,map_mul,Nat.cast_mul]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramGcdSource -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma gcd_generator_left (I J : SupportedIdeal) :
    primaryGenerator I.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdLeft I J).val := by
  rw [←primaryGenerator_mul,gcd_common_left]

lemma gcd_generator_right (I J : SupportedIdeal) :
    primaryGenerator J.val=primaryGenerator (gcdCommon I J).val*primaryGenerator (gcdRight I J).val := by
  rw [←primaryGenerator_mul,gcd_common_right]

lemma gcd_generator_coprime (I J : SupportedIdeal) :
    IsCoprime (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).1]
  exact gcd_residual_coprime I J

theorem actual_gcd_lift (I J : SupportedIdeal) (k : O) :
    let C:=primaryGenerator (gcdCommon I J).val
    let n₁:=primaryGenerator (gcdLeft I J).val
    let n₂:=primaryGenerator (gcdRight I J).val
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)=
      idealRowHom k (gcdLeft I J).val*star (idealRowHom (-k) (gcdRight I J).val)*
        sexticReciprocityPhase n₁ n₂*
          actualCommon C ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property) n₁ n₂ k := by
  dsimp only
  have h₁ := (supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property
  have h₂ := (supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property
  have hp₁ : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator (gcdLeft I J).val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).2
  have hp₂ : ConcretePrimeRowBridge.goodLambda^2∣primaryGenerator (gcdRight I J).val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).2
  have hh := actual_common_lift (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val) k
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property) h₁ h₂ hp₁ hp₂
    (gcd_generator_coprime I J)
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdLeft I J).property)).1,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ (gcdRight I J).property)).1] using hh

theorem actual_gcd_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑'k : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (primaryGenerator (gcdCommon I J).val*k)*
        paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator (gcdCommon I J).val*k)‖^2/
          ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hneg := (Equiv.neg O).tsum_eq (fun h : O=>
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) h*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simp only [Equiv.neg_apply,map_neg,norm_neg] at hneg
  rw [hneg]
  have hh := actual_common_frequency_tsum (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val)
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=>paperRadialFourier U (Q*‖eisEmbedding h‖^2/
      ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramPrimaryLattice -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev PrimaryElement := {n : O // Supported (Ideal.span {n}) ∧ λ₀^2∣n-1}

def primaryIdealEquiv : SupportedIdeal≃PrimaryElement where
  toFun I := ⟨primaryGenerator I.val,(supported_span_primaryGenerator_iff _).mpr I.property,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2⟩
  invFun n := ⟨Ideal.span {n.val},n.property.1⟩
  left_inv I := Subtype.ext (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1
  right_inv n := Subtype.ext (primaryGenerator_span n.val (supported_element_ne_zero _ n.property.1) n.property.2)

lemma primaryCoefficient_nonzero_supported (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (n : O) (hn : primaryCoefficient S hS σ n≠0) :
    Supported (Ideal.span {n}) ∧ λ₀^2∣n-1 := by
  have hp : λ₀^2∣n-1 := by
    by_contra h
    exact hn (by simp [primaryCoefficient,h])
  have hc : IsCoprime (calibrationForSet S hS).generator n := by
    by_contra h
    exact hn (by rw [primaryCoefficient,ite_eq_left hp,gramCoefficientExtension_zero S hS σ n h])
  have hb := calibration_generator_bad S hS hbad
  exact ⟨supported_of_coprime_bad _ n hb.1 hb.2 hc,hp⟩

lemma primary_factor_right (A n : O) (hA : λ₀^2∣A-1) (hAn : λ₀^2∣A*n-1) : λ₀^2∣n-1 := by
  have h := dvd_sub hAn (hA.mul_right n)
  convert h using 1 ; ring

lemma primaryCoefficient_residual (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (A n : O) (hA : λ₀^2∣A-1)
    (hn : primaryCoefficient S hS σ (A*n)≠0) :
    Supported (Ideal.span {n}) ∧ λ₀^2∣n-1 := by
  have hs := primaryCoefficient_nonzero_supported S hS hbad σ (A*n) hn
  have hsp : Supported (Ideal.span {A}*Ideal.span {n}) := by
    rw [Ideal.span_singleton_mul_span_singleton]
    exact hs.1
  exact ⟨((supported_mul_iff _ _).mp hsp).2,primary_factor_right A n hA hs.2⟩

theorem primary_ideal_tsum (f : O→ℂ)
    (hz : ∀n,¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)→f n=0) :
    (∑'I : SupportedIdeal,f (primaryGenerator I.val))=∑'n : O,f n := by
  have he := primaryIdealEquiv.tsum_eq (fun n : PrimaryElement=>f n.val)
  change (∑'I : SupportedIdeal,f (primaryGenerator I.val))=∑'n : PrimaryElement,f n.val at he
  rw [he]
  exact tsum_subtype_eq_of_support_subset (by intro n hn;by_contra h;exact hn (hz n h))

theorem primary_ideal_pair_tsum (f : O→O→ℂ)
    (hl : ∀n m,¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)→f n m=0)
    (hr : ∀n m,¬(Supported (Ideal.span {m}) ∧ λ₀^2∣m-1)→f n m=0) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,f (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : O,∑'m : O,f n m := by
  have hinner (n : O) : (∑'J : SupportedIdeal,f n (primaryGenerator J.val))=∑'m : O,f n m :=
    primary_ideal_tsum (fun m=>f n m) (fun m h=>hr n m h)
  simp_rw [hinner]
  apply primary_ideal_tsum (fun n=>∑'m : O,f n m)
  intro n hn
  simp only [hl n _ hn,tsum_zero]

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramLatticeSource -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma jointExtension_zero_off_primary_left (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n m : O) (hn : ¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*n))=0 := by
    by_contra h
    apply hn
    apply primaryCoefficient_residual S hS hbad σ (C*d) n hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,zero_mul]

lemma jointExtension_zero_off_primary_right (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n m : O) (hm : ¬(Supported (Ideal.span {m}) ∧ λ₀^2∣m-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  have hz : primaryCoefficient S hS σ (C*(d*m))=0 := by
    by_contra h
    apply hm
    apply primaryCoefficient_residual S hS hbad σ (C*d) m hCd
    simpa only [mul_assoc] using h
  simp only [jointExtension,jointFixed,hz,star_zero,mul_zero,zero_mul]

theorem jointExtension_ideal_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O)
    (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (W : O→O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      jointExtension S hS σ C k u a b r hr P hg c (d*primaryGenerator I.val) (d*primaryGenerator J.val)*
        W (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : O,∑'m : O,jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m := by
  apply primary_ideal_pair_tsum (fun n m=>jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m)
  · intro n m hn
    rw [jointExtension_zero_off_primary_left S hS hbad σ C k d hCd u a b r hr P hg c n m hn,zero_mul]
  · intro n m hm
    rw [jointExtension_zero_off_primary_right S hS hbad σ C k d hCd u a b r hr P hg c n m hm,zero_mul]

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramMobiusLattice -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_product (C d : O) (hC : λ₀^2∣C-1) (hd : λ₀^2∣d-1) : λ₀^2∣C*d-1 := by
  have h := dvd_add (hC.mul_right d) hd
  convert h using 1 ; ring

theorem jointExtension_divisor_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (D : SupportedIdeal) (W : O→O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          W (primaryGenerator I.val) (primaryGenerator J.val) else 0)=
      ∑'n : O,∑'m : O,
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D.val*n) (primaryGenerator D.val*m)*
          W (primaryGenerator D.val*n) (primaryGenerator D.val*m) := by
  rw [supported_divisor_pair_tsum D (fun I J=>
    jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
      W (primaryGenerator I.val) (primaryGenerator J.val))]
  simp only [supported_dilation_generator]
  have hd : λ₀^2∣primaryGenerator D.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ D.property)).2
  exact jointExtension_ideal_lattice S hS hbad σ C k (primaryGenerator D.val) (primary_product C _ hC hd)
    u a b r hr P hg c (fun n m=>W (primaryGenerator D.val*n) (primaryGenerator D.val*m))

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramPhysicalScale -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

 def residualScale (C D : SupportedIdeal) (Y : ℝ) : ℝ :=
  Y/((Ideal.absNorm C.val:ℝ)*Ideal.absNorm D.val)

lemma residualScale_pos (C D : SupportedIdeal) (Y : ℝ) (hY : 0<Y) : 0< residualScale C D Y := by
  have hc : (0:ℝ)<Ideal.absNorm C.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1)
  have hd : (0:ℝ)<Ideal.absNorm D.val := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.property.1)
  exact div_pos hY (mul_pos hc hd)

lemma residual_column_ratio (C D I : SupportedIdeal) (Y : ℝ) (hY : 0<Y) :
    (Ideal.absNorm (supportedIdealProduct C (supportedIdealProduct D I)).val:ℝ)/Y=
      (Ideal.absNorm I.val:ℝ)/residualScale C D Y := by
  simp only [supportedIdealProduct,map_mul,Nat.cast_mul,residualScale]
  field_simp

 def frequencyScale (C : SupportedIdeal) (k : O) (Y Q : ℝ) : ℝ :=
  (Ideal.absNorm C.val:ℝ)*‖eisEmbedding k‖^2/(Y^2/Q)

lemma frequencyScale_nonneg (C : SupportedIdeal) (k : O) (Y Q : ℝ) (hQ : 0≤Q) :
    0≤frequencyScale C k Y Q := by unfold frequencyScale;positivity

theorem original_kernel_residual_scale (C D I J : SupportedIdeal) (k : O)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) :
    Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
      ‖eisEmbedding (primaryGenerator (supportedIdealProduct C (supportedIdealProduct D I)).val*
        primaryGenerator (supportedIdealProduct C (supportedIdealProduct D J)).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/residualScale C D Y)*((Ideal.absNorm J.val:ℝ)/residualScale C D Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ _ _ (primaryGenerator C.val*k),
    residual_column_ratio C D I Y hY,residual_column_ratio C D J Y hY]
  rw [map_mul,norm_mul,mul_pow,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec C.val (supported_primaryGenerator_ne_zero C.val C.property)).1]
  unfold frequencyScale
  ring

lemma physicalPoint_first_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).1‖^2=‖eisEmbedding m.1‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

lemma physicalPoint_second_norm (N : ℝ) (hN : 0<N) (m : O×O) :
    ‖(WithLp.ofLp (ProbeGramLatticeDecay.physicalPoint N m)).2‖^2=‖eisEmbedding m.2‖^2/N := by
  simp only [ProbeGramLatticeDecay.physicalPoint,ProbeGramLatticeDecay.point,WithLp.ofLp_toLp]
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.sqrt_pos.mpr hN),div_pow,Real.sq_sqrt hN.le]

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramSourceBlock -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma jointProfile_physicalPoint (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (v T : ℝ) (hT : 0≤T) (N : ℝ) (hN : 0<N) (m : O×O) :
    ProbeGramJointConstruction.jointProfile W U a b ha hab hs hW v T hT
      (ProbeGramLatticeDecay.physicalPoint N m)=
      shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N) := by
  rw [ProbeGramJointConstruction.jointProfile_apply]
  unfold ProbeGramJointConstruction.rawProfile ProbeGramJointConstruction.q1 ProbeGramJointConstruction.q2
  change lowGramProfile W v _ * star (lowGramProfile W v _) * _ = _
  have h₁ : ‖WithLp.fst (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.1‖^2/N := physicalPoint_first_norm N hN m
  have h₂ : ‖WithLp.snd (ProbeGramLatticeDecay.physicalPoint N m)‖^2=‖eisEmbedding m.2‖^2/N := physicalPoint_second_norm N hN m
  rw [h₁,h₂]
  rfl

theorem literal_nonexceptional_source (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤ c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(U : SchwartzMap ℝ ℂ)(v T : ℝ),0≤T→∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H₀,K₀,hK₀,hblock⟩ := literal_nonexceptional_block A hA a₀ b₀ ha₀ hab
  obtain ⟨J,H,hprofile⟩ := ProbeGramJointProfile.jointProfile_uniform_degree a₀ b₀ ha₀ hab B H₀
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K₁,hK₁,hprofile⟩ := hprofile W hs hW
  refine ⟨K₀*K₁,mul_pos hK₀ hK₁,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he U v T hT d N hN
  let V := ProbeGramJointConstruction.jointProfile W U a₀ b₀ ha₀ hab hs hW v T hT
  have hv := ProbeGramJointConstruction.jointProfile_annularSupport W U a₀ b₀ ha₀ hab hs hW v T hT
  have hb := hblock S hS σ C k hC hk0 u a b r hr hk P hg c hc hfac p hp0 hgp hchar hfixed hcommon he V hv d N hN
  have hfun : (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
      V (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
    funext m
    rw [jointProfile_physicalPoint W U a₀ b₀ ha₀ hab hs hW v T hT N hN m]
  rw [hfun] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hm : 0≤ min (1:ℝ) (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
      Ideal.absNorm (Ideal.span {k})/N)^A) := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hprofile U v T hT) hK₀.le)
        (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {C})))) (sq_nonneg N)) hm
  convert hh using 1 ; ring

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramWindowMobius -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma primary_norm (I : SupportedIdeal) :
    ‖eisEmbedding (primaryGenerator I.val)‖^2=(Ideal.absNorm I.val:ℝ) := by
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1]

lemma shell_dilated_column (D I : SupportedIdeal) (N : ℝ) :
    (Ideal.absNorm (supportedIdealProduct D I).val:ℝ)/N=
      ‖eisEmbedding (primaryGenerator I.val)‖^2/(N/Ideal.absNorm D.val) := by
  rw [primary_norm,supported_dilation_norm,Nat.cast_mul]
  rw [div_div_eq_mul_div]
  ring

lemma shell_window_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (I J : SupportedIdeal)
    (h : I∉lowGaussColumns W hW N hN ∨ J∉lowGaussColumns W hW N hN) :
    shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [lowGaussColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [lowGaussColumns_mem,not_not] using h

theorem original_window_mobius_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k : O) (hC : λ₀^2∣C-1)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) :
    (∑I∈lowGaussColumns W hW N hN,∑J∈lowGaussColumns W hW N hN,
      if IsCoprime I.val J.val then
        jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator I.val) (primaryGenerator J.val)*
          shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N) else 0)=
      ∑D∈divisorPool (lowGaussColumns W hW N hN) Subtype.val,(moebius D:ℂ)*
        ∑'n : O,∑'m : O,
          jointExtension S hS σ C k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
            shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
              (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  let F := lowGaussColumns W hW N hN
  let f := fun I J : SupportedIdeal=>jointExtension S hS σ C k u a b r hr P hg c
    (primaryGenerator I.val) (primaryGenerator J.val)*
      shellProfile W v U T ((Ideal.absNorm I.val:ℝ)/N) ((Ideal.absNorm J.val:ℝ)/N)
  have hf : ∀I J,I∉F ∨ J∉F→f I J=0 := by
    intro I J h
    dsimp [f]
    rw [shell_window_support W hW N hN U v T I J h,mul_zero]
  change (∑I∈F,∑J∈F,if IsCoprime I.val J.val then f I J else 0)=_
  rw [finite_pair_mobius_dilation F F f hf]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  let D₀ := poolDivisor F D
  have hd : D₀.val=D := poolDivisor_val F D hD
  have hdp : λ₀^2∣primaryGenerator D₀.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ D₀.property)).2
  have he := jointExtension_ideal_lattice S hS hbad σ C k (primaryGenerator D₀.val)
    (primary_product C _ hC hdp) u a b r hr P hg c
    (fun n m=>shellProfile W v U T (‖eisEmbedding n‖^2/(N/Ideal.absNorm D₀.val))
      (‖eisEmbedding m‖^2/(N/Ideal.absNorm D₀.val)))
  dsimp only [f]
  simp only [supported_dilation_generator,shell_dilated_column]
  convert he using 1
  rw [hd]

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramCommonSource -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

def commonResidualScale (C : SupportedIdeal) (Y : ℝ) : ℝ := Y/Ideal.absNorm C.val
lemma commonResidualScale_pos (C : SupportedIdeal) (Y : ℝ) (hY : 0<Y) : 0<commonResidualScale C Y :=
  div_pos hY (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr C.property.1))
lemma common_column_ratio (C I : SupportedIdeal) (Y : ℝ) :
    (Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y=(Ideal.absNorm I.val:ℝ)/commonResidualScale C Y := by
  rw [supported_dilation_norm,Nat.cast_mul,commonResidualScale,div_div_eq_mul_div]
  ring
lemma common_kernel_scale (C I J : SupportedIdeal) (k : O) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) :
    Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
      ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2=
      frequencyScale C k Y Q/
        (((Ideal.absNorm I.val:ℝ)/commonResidualScale C Y)*((Ideal.absNorm J.val:ℝ)/commonResidualScale C Y)) := by
  rw [lowGram_kernel_scale Y Q hY hQ,common_column_ratio,common_column_ratio,
    map_mul,norm_mul,mul_pow,primary_norm]
  unfold frequencyScale
  ring

theorem original_common_window_source (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : O)
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤ c i) (hcop : Pairwise (Function.onFun IsCoprime P)) (he : C.val=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    let N:=commonResidualScale C Y
    let hN:=commonResidualScale_pos C Y hY
    let F:=lowGaussColumns W hW N hN
    (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)=
      ∑D∈divisorPool F Subtype.val,(moebius D:ℂ)*∑'n : O,∑'m : O,
        jointExtension S hS σ (primaryGenerator C.val) k u a b r hr P hg c (primaryGenerator D*n) (primaryGenerator D*m)*
          shellProfile W v U (frequencyScale C k Y Q) (‖eisEmbedding n‖^2/(N/Ideal.absNorm D))
            (‖eisEmbedding m‖^2/(N/Ideal.absNorm D)) := by
  dsimp only
  have hpc : λ₀^2∣primaryGenerator C.val-1 :=
    (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).2
  rw [←original_window_mobius_lattice S hS hbad σ (primaryGenerator C.val) k hpc
    u a b r hr P hg c W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)
    U v (frequencyScale C k Y Q)]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs with hIJ
  · have hni : Supported (Ideal.span {primaryGenerator I.val}) := (supported_span_primaryGenerator_iff _).mpr I.property
    have hnj : Supported (Ideal.span {primaryGenerator J.val}) := (supported_span_primaryGenerator_iff _).mpr J.property
    have hpi : λ₀^2∣primaryGenerator I.val-1 := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).2
    have hpj : λ₀^2∣primaryGenerator J.val-1 := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).2
    have hij : IsCoprime (primaryGenerator I.val) (primaryGenerator J.val) := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      simpa only [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1,
        (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).1] using hIJ
    have hf : Ideal.span {primaryGenerator C.val}=∏i,P i^c i := by
      rw [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1,he]
    rw [jointExtension_source S hS σ (primaryGenerator C.val) k
      ((supported_span_primaryGenerator_iff _).mpr C.property) u a b r hr hpr hk P hg c hc hcop hf
      _ _ hni hnj hpi hpj hij]
    rw [lowGramCoefficient_eq_primary S hS hbad σ,lowGramCoefficient_eq_primary S hS hbad σ,
      common_kernel_scale C I J k Y Q hY hQ,common_column_ratio,common_column_ratio]
    simp only [supported_dilation_generator,shellProfile,star_mul]
    ring
  · rfl

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramCanonical -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev GramFrequency := {k : O // k≠0}
abbrev GramPrime (C : SupportedIdeal) := {P : Id // P∈IdealMobiusDivisorSum.primeSupport C.val}
def gramPrime (C : SupportedIdeal) (P : GramPrime C) : Id := P.val
instance gramPrimeMaximal (C : SupportedIdeal) (P : GramPrime C) : (gramPrime C P).IsMaximal :=
  (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal (support_prime P.property).ne_zero

def gramExponent (C : SupportedIdeal) (P : GramPrime C) : ℕ := (normalizedFactors C.val).count P.val
lemma gramExponent_pos (C : SupportedIdeal) (P : GramPrime C) : 1≤gramExponent C P :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property)
lemma gramPrime_good (C : SupportedIdeal) (P : GramPrime C) : λ₀∉gramPrime C P :=
  (supported_factors_good C.val C.property P.val (Multiset.mem_toFinset.mp P.property)).2.1
lemma gramPrime_coprime (C : SupportedIdeal) : Pairwise (Function.onFun IsCoprime (gramPrime C)) := by
  intro P Q hpq
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hpq)
lemma gramPrime_product (C : SupportedIdeal) : C.val=∏P : GramPrime C,gramPrime C P^gramExponent C P := by
  calc
    C.val=(normalizedFactors C.val).prod := (Ideal.prod_normalizedFactors_eq_self C.property.1).symm
    _=∏P∈IdealMobiusDivisorSum.primeSupport C.val,P^(normalizedFactors C.val).count P := Finset.prod_multiset_count _
    _=_ := (Finset.prod_coe_sort _ _).symm

instance gramPrimePowerFinite (C : SupportedIdeal) (P : GramPrime C) :
    Finite (O⧸gramPrime C P^gramExponent C P) :=
  Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ (support_prime P.property).ne_zero)
instance gramPrimePowerFintype (C : SupportedIdeal) (P : GramPrime C) :
    Fintype (O⧸gramPrime C P^gramExponent C P) := Fintype.ofFinite _
instance gramProductFinite (C : SupportedIdeal) : Finite (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  rw [←gramPrime_product C]
  exact C.property.1
instance gramProductFintype (C : SupportedIdeal) : Fintype (O⧸∏P : GramPrime C,gramPrime C P^gramExponent C P) := Fintype.ofFinite _

structure GramNumeratorData (k : GramFrequency) where
  unit : Oˣ
  lambdaExponent : ℕ
  twoExponent : ℕ
  good : O
  supported : Supported (Ideal.span {good})
  primary : λ₀^2∣good-1
  factor : k.val=unit.val*λ₀^lambdaExponent*(2:O)^twoExponent*good

lemma gramNumeratorData_nonempty (k : GramFrequency) : Nonempty (GramNumeratorData k) := by
  obtain ⟨u,a,b,r,hr,hpr,hf⟩ := exists_supported_numerator_factorization k.val k.property
  exact ⟨⟨u,a,b,r,hr,hpr,hf⟩⟩
def gramNumeratorData (k : GramFrequency) : GramNumeratorData k := Classical.choice (gramNumeratorData_nonempty k)

def canonicalJoint (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ℂ :=
  let f:=gramNumeratorData k
  jointExtension S hS σ (primaryGenerator C.val) k.val f.unit f.lambdaExponent f.twoExponent
    f.good f.supported (gramPrime C) (gramPrime_good C) (gramExponent C) n m

lemma canonicalJoint_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (n m : O) : ‖canonicalJoint S hS σ C k n m‖≤(Ideal.absNorm C.val:ℝ) := by
  have hh := jointExtension_norm S hS σ (primaryGenerator C.val) k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramPrime C) (gramPrime_good C)
    (gramExponent C) (gramExponent_pos C) n m
  simpa only [←gramPrime_product C,canonicalJoint] using hh

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramClassification -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def exceptionalModulus (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) : Id :=
  jointFixedModulus S hS*C.val
lemma exceptionalModulus_nonzero (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    exceptionalModulus S hS C≠0 := mul_ne_zero (jointFixedModulus_nonzero S hS) C.property.1
lemma exceptionalModulus_norm (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) :
    Ideal.absNorm (exceptionalModulus S hS C)=Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm C.val :=
  map_mul Ideal.absNorm _ _

def ExceptionalFrequency (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency) : Prop :=
  ∀p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C),valuation (Ideal.span {k.val}) p%6=0

lemma nonexceptional_prime (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal) (k : GramFrequency)
    (hk : ¬ExceptionalFrequency S hS C k) :
    ∃p : Id,Prime p ∧ p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C) ∧
      ¬6∣(normalizedFactors (Ideal.span {k.val})).count p := by
  unfold ExceptionalFrequency at hk
  push Not at hk
  obtain ⟨p,hp,he⟩ := hk
  have hcount : (normalizedFactors (Ideal.span {k.val})).count p≠0 := by
    intro hz
    apply he
    simp [valuation,hz]
  have hprime := prime_of_normalized_factor p (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount))
  exact ⟨p,hprime,hp,fun hd=>he (Nat.mod_eq_zero_of_dvd hd)⟩

lemma outside_exceptional_not_dvd (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    (¬p∣jointFixedModulus S hS) ∧ (¬p∣∏i : GramPrime C,gramPrime C i) := by
  have hnot : ¬p∣exceptionalModulus S hS C := by
    intro hd
    apply hout
    exact Multiset.mem_toFinset.mpr ((Ideal.mem_normalizedFactors_iff (exceptionalModulus_nonzero S hS C)).mpr
      ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩)
  refine ⟨fun hd=>hnot (dvd_mul_of_dvd_left hd _),?_⟩
  intro hd
  apply hnot
  apply dvd_mul_of_dvd_right
  apply dvd_trans hd
  calc
    _∣∏i : GramPrime C,gramPrime C i^gramExponent C i :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (gramExponent_pos C i)))
    _=C.val := (gramPrime_product C).symm

lemma outside_exceptional_good (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (C : SupportedIdeal)
    (p : Id) (hp : Prime p) (hout : p∉IdealMobiusDivisorSum.primeSupport (exceptionalModulus S hS C)) :
    λ₀∉p ∧ ringChar (O⧸p)≠2 := by
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hle : exceptionalModulus S hS C≤Ideal.span {(72:O)} :=
    le_trans Ideal.mul_le_left Ideal.mul_le_right
  have hh := CenteredExceptionalProfile.outside_fixed_support _ (exceptionalModulus_nonzero S hS C) hle p hp hout
  exact ⟨hh.1,ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem p hh.2.1⟩

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramCanonicalBlock -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def canonicalLatticeBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (d : O) (W : ℝ→ℂ) (U : SchwartzMap ℝ ℂ)
    (v T N : ℝ) : ℂ :=
  ∑'m : O×O,canonicalJoint S hS σ C k (d*m.1) (d*m.2)*
    shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)

theorem canonical_nonexceptional_block (A B : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v T N : ℝ),0≤T→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*
            Ideal.absNorm (Ideal.span {k.val})/N)^A) := by
  obtain ⟨J,H,hsource⟩ := literal_nonexceptional_source A B hA a₀ b₀ ha₀ hab
  refine ⟨J,H,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hsource⟩ := hsource W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v T N hT hN
  obtain ⟨p,hp,hout,he⟩ := nonexceptional_prime S hS C k hk
  let : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := outside_exceptional_good S hS C p hp hout
  have hd := outside_exceptional_not_dvd S hS C p hp hout
  have hcspan := (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ C.property)).1
  have hf : Ideal.span {primaryGenerator C.val}=∏i : GramPrime C,gramPrime C i^gramExponent C i := hcspan.trans (gramPrime_product C)
  have hh := hsource S hS σ (primaryGenerator C.val) k.val
    (supported_primaryGenerator_ne_zero _ C.property) k.property
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).factor
    (gramPrime C) (gramPrime_good C) (gramExponent C) (gramExponent_pos C) hf
    p hp.ne_zero hg.1 hg.2 hd.1 hd.2 he U v T hT d N hN
  simpa only [canonicalLatticeBlock,canonicalJoint,hcspan] using hh.2

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramCanonicalSource -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcreteTraceCRT CenteredMomentMobiusRegroup UniqueFactorizationMonoid
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def originalCommonBlock (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  let N:=commonResidualScale C Y
  let hN:=commonResidualScale_pos C Y hY
  let F:=lowGaussColumns W hW N hN
  (∑I∈F,∑J∈F,if IsCoprime I.val J.val then
      (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
      star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y))*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val)
        (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property)
        (primaryGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k.val)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2)
      else 0)

theorem originalCommonBlock_eq_lattice (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C : SupportedIdeal) (k : GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,
        (moebius D:ℂ)*canonicalLatticeBlock S hS σ C k (primaryGenerator D) W U v
          (frequencyScale C k.val Y Q) (commonResidualScale C Y/Ideal.absNorm D) := by
  have hh := original_common_window_source S hS hbad σ C k.val
    (gramNumeratorData k).unit (gramNumeratorData k).lambdaExponent (gramNumeratorData k).twoExponent
    (gramNumeratorData k).good (gramNumeratorData k).supported (gramNumeratorData k).primary
    (gramNumeratorData k).factor (gramPrime C) (gramPrime_good C) (gramExponent C)
    (gramExponent_pos C) (gramPrime_coprime C) (gramPrime_product C) W hW Y Q hY hQ U v
  change originalCommonBlock S hS σ C k W hW Y Q hY U v=_ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hD0 := (divisorPool_supported _ D hD).1
  have hN : 0<commonResidualScale C Y/(Ideal.absNorm D:ℝ) :=
    div_pos (commonResidualScale_pos C Y hY) (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
  exact (shell_lattice_summable W hW _ hN U v (frequencyScale C k.val Y Q)
    (fun n m=>canonicalJoint S hS σ C k (primaryGenerator D*n) (primaryGenerator D*m))).tsum_prod.symm

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramCanonicalTrivial -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem canonical_trivial_block (a b B : ℝ) (ha : 0<a) (hb : 0≤b) (hB : 0≤B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤B)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency)(d : O)(N T v : ℝ),0<N→0≤T→
      (1+T)^A*‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2 := by
  obtain ⟨s,K,hK,hprofile⟩ := shellProfile_weighted_bound a b B ha hB A
  refine ⟨s,(1+128*b)^2*K,by positivity,?_⟩
  intro W hcompact hs hW U S hS σ C k d N T v hN hT
  let F:=shellLatticeColumns W hcompact N hN
  let G:=F
  have hF0 : ∀z∈F,z≠0 := shellLatticeColumns_nonzero W hcompact N hN a b ha hs
  have hG0 : ∀z∈G,z≠0 := hF0
  have hFN : ∀z∈F,‖eisEmbedding z‖^2≤b*N := shellLatticeColumns_norm W hcompact N hN a b hs
  have hGN : ∀z∈G,‖eisEmbedding z‖^2≤b*N := hFN
  unfold canonicalLatticeBlock
  rw [shell_lattice_tsum W hcompact N hN U v T (fun n m=>canonicalJoint S hS σ C k (d*n) (d*m))]
  have hcoef (n m : O) : ‖canonicalJoint S hS σ C k (d*n) (d*m)‖≤(Ideal.absNorm C.val:ℝ) :=
    canonicalJoint_norm S hS σ C k _ _
  have hpoint (n m : O) : (1+T)^A*‖canonicalJoint S hS σ C k (d*n) (d*m)*
      shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖≤
      (Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    rw [norm_mul]
    calc
      _ = ‖canonicalJoint S hS σ C k (d*n) (d*m)‖*
          ((1+T)^A*‖shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖) := by ring
      _ ≤ _ := mul_le_mul (hcoef n m) (hprofile W hs hW U v T _ _ hT) (by positivity) (by positivity)
  have hcount := annular_pair_count F G b N hb hN.le hF0 hG0 hFN hGN
  calc
    _ ≤ (1+T)^A*(∑n∈F,∑m∈G,‖canonicalJoint S hS σ C k (d*n) (d*m)*
        shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _=>norm_sum_le _ _)
    _ ≤ (F.card:ℝ)*G.card*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      simp_rw [Finset.mul_sum]
      calc
        _ ≤ ∑n∈F,∑m∈G,(Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) :=
          Finset.sum_le_sum (fun n _=>Finset.sum_le_sum (fun m _=>hpoint n m))
        _ = _ := by simp;ring
    _ ≤ ((128*b)^2*N^2)*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Finset.card_product,Nat.cast_mul] using hcount
    _ ≤ _ := by
      have hb' : (128*b)^2≤(1+128*b)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hb' (show 0≤N^2*((Ideal.absNorm C.val:ℝ)*
        (K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) by positivity)]

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramFiniteGcd -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma supportedIdealProduct_injective (C : SupportedIdeal) : Function.Injective (supportedIdealProduct C) := by
  intro I J h
  apply Subtype.ext
  exact mul_left_cancel₀ C.property.1 (congrArg Subtype.val h)

def commonPool (F : Finset SupportedIdeal) : Finset SupportedIdeal :=
  (F×ˢF).image (fun p=>gcdCommon p.1 p.2)
def commonColumns (F : Finset SupportedIdeal) (C : SupportedIdeal) : Finset SupportedIdeal :=
  F.preimage (supportedIdealProduct C) (supportedIdealProduct_injective C).injOn
lemma commonColumns_mem (F : Finset SupportedIdeal) (C I : SupportedIdeal) :
    I∈commonColumns F C ↔ supportedIdealProduct C I∈F := Finset.mem_preimage

def commonTriples (F : Finset SupportedIdeal) : Finset ((_C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)) :=
  (commonPool F).sigma (fun C=>(commonColumns F C×ˢcommonColumns F C).filter (fun p=>IsCoprime p.1.val p.2.val))

theorem finite_pair_gcd (F : Finset SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈F,∑J∈F,f I J)=
      ∑C∈commonPool F,∑I∈commonColumns F C,∑J∈commonColumns F C,
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  have he : (∑p∈F×ˢF,f p.1 p.2)=
      ∑t∈commonTriples F,f (supportedIdealProduct t.1 t.2.1) (supportedIdealProduct t.1 t.2.2) := by
    apply Finset.sum_bij (fun p _=>⟨gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2⟩)
    · intro p hp
      have hl : supportedIdealProduct (gcdCommon p.1 p.2) (gcdLeft p.1 p.2)=p.1 := Subtype.ext (gcd_common_left _ _)
      have hr : supportedIdealProduct (gcdCommon p.1 p.2) (gcdRight p.1 p.2)=p.2 := Subtype.ext (gcd_common_right _ _)
      simp only [commonTriples,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product,commonColumns_mem]
      exact ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,⟨by rw [hl];exact (Finset.mem_product.mp hp).1,by rw [hr];exact (Finset.mem_product.mp hp).2⟩,gcd_residual_coprime _ _⟩
    · intro p hp q hq he
      have hc := congrArg Sigma.fst he
      have hl := congrArg (fun t : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)=>t.2.1) he
      have hr := congrArg (fun t : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal)=>t.2.2) he
      apply Prod.ext <;> apply Subtype.ext
      · rw [←gcd_common_left p.1 p.2,←gcd_common_left q.1 q.2]
        rw [show gcdCommon p.1 p.2=gcdCommon q.1 q.2 from hc,show gcdLeft p.1 p.2=gcdLeft q.1 q.2 from hl]
      · rw [←gcd_common_right p.1 p.2,←gcd_common_right q.1 q.2]
        rw [show gcdCommon p.1 p.2=gcdCommon q.1 q.2 from hc,show gcdRight p.1 p.2=gcdRight q.1 q.2 from hr]
    · intro t ht
      have ht' : t.1∈commonPool F ∧ (t.2.1∈commonColumns F t.1 ∧ t.2.2∈commonColumns F t.1) ∧ IsCoprime t.2.1.val t.2.2.val := by
        simpa only [commonTriples,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product] using ht
      let u : CoprimeTriple:=⟨(t.1,t.2),ht'.2.2⟩
      refine ⟨(supportedIdealProduct t.1 t.2.1,supportedIdealProduct t.1 t.2.2),?_,?_⟩
      · exact Finset.mem_product.mpr ⟨(commonColumns_mem F _ _).mp ht'.2.1.1,(commonColumns_mem F _ _).mp ht'.2.1.2⟩
      · have h:=congrArg Subtype.val (gcdTriple_multiply u)
        exact congrArg (fun p : SupportedIdeal×(SupportedIdeal×SupportedIdeal)=>(⟨p.1,p.2⟩ : (C : SupportedIdeal)×(SupportedIdeal×SupportedIdeal))) h
    · intro p hp
      have hl : supportedIdealProduct (gcdCommon p.1 p.2) (gcdLeft p.1 p.2)=p.1 := Subtype.ext (gcd_common_left _ _)
      have hr : supportedIdealProduct (gcdCommon p.1 p.2) (gcdRight p.1 p.2)=p.2 := Subtype.ext (gcd_common_right _ _)
      simp only [hl,hr]
  rw [Finset.sum_product] at he
  rw [he,commonTriples,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.sum_filter,Finset.sum_product]

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramNonzeroFrequency -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma nonzero_tsum_indicator (f : O→ℂ) :
    (∑'k : O,if k=0 then 0 else f k)=∑'k : GramFrequency,f k.val := by
  rw [←tsum_subtype_eq_of_support_subset (s:={k : O | k≠0}) (by
    intro k hk hz
    subst k
    exact hk (by simp))]
  apply tsum_congr
  intro k
  exact ite_eq_right k.property

def gramFrequencyNeg : GramFrequency≃GramFrequency where
  toFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  invFun k:=⟨-k.val,neg_ne_zero.mpr k.property⟩
  left_inv k:=Subtype.ext (neg_neg k.val)
  right_inv k:=Subtype.ext (neg_neg k.val)

lemma actual_common_nonzero_tsum (C n₁ n₂ : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (F : O→ℂ) :
    (∑'j : GramFrequency,actualCorrelation (C*n₁) (C*n₂)
      (supported_mul_elements C n₁ hC h₁) (supported_mul_elements C n₂ hC h₂) j.val*F j.val)=
      ∑'k : GramFrequency,actualCorrelation (C*n₁) (C*n₂)
        (supported_mul_elements C n₁ hC h₁) (supported_mul_elements C n₂ hC h₂) (C*k.val)*F (C*k.val) := by
  have hh := actual_common_frequency_tsum C n₁ n₂ hC h₁ h₂ (fun j=>if j=0 then 0 else F j)
  have hc0 := supported_element_ne_zero C hC
  simp only [mul_ite,mul_zero,mul_eq_zero,hc0,false_or] at hh
  simpa only [nonzero_tsum_indicator] using hh

lemma actual_gcd_nonzero_frequency_source (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) :
    (∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
      paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑'k : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (primaryGenerator (gcdCommon I J).val*k.val)*
        paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator (gcdCommon I J).val*k.val)‖^2/
          ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hn := gramFrequencyNeg.tsum_eq (fun h : GramFrequency=>
    actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) h.val*
      paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simp only [gramFrequencyNeg,Equiv.coe_fn_mk,map_neg,norm_neg] at hn
  rw [hn]
  have hh := actual_common_nonzero_tsum (primaryGenerator (gcdCommon I J).val)
    (primaryGenerator (gcdLeft I J).val) (primaryGenerator (gcdRight I J).val)
    ((supported_span_primaryGenerator_iff _).mpr (gcdCommon I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdLeft I J).property)
    ((supported_span_primaryGenerator_iff _).mpr (gcdRight I J).property)
    (fun h=>paperRadialFourier U (Q*‖eisEmbedding h‖^2/
      ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))
  simpa only [←gcd_generator_left I J,←gcd_generator_right I J] using hh

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramWeightedFrequency -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma min_product_amplification (L T : ℝ) (hL : 0≤L) (hT : 0≤T) (A : ℕ) :
    min 1 ((L*T)^A)≤(1+T)^A*min 1 (L^A) := by
  by_cases h : L^A≤1
  · rw [min_eq_right h]
    apply (min_le_right _ _).trans
    rw [mul_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT (by linarith) _) (pow_nonneg hL _)
  · rw [min_eq_left (le_of_not_ge h),mul_one]
    exact (min_le_left _ _).trans (one_le_pow₀ (by linarith))

lemma frequencyScale_ratio (C : SupportedIdeal) (k : GramFrequency) (Y Q : ℝ) :
    frequencyScale C k.val Y Q=(Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/Ideal.absNorm C.val) := by
  rw [frequencyScale,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,div_div_eq_mul_div]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem canonical_nonexceptional_weighted (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency),¬ExceptionalFrequency S hS C k→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)*
          (1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_block A (A+2) hA a₀ b₀ ha₀ hab
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K,hK,?_⟩
  intro S hS σ C k hk d U v H N hH hN
  let t : ℝ := (Ideal.absNorm (Ideal.span {k.val}):ℝ)/H
  let L : ℝ := (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N
  have ht : 0≤t := by dsimp [t];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have htp : 0<1+t := by linarith
  have he : (Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*Ideal.absNorm (Ideal.span {k.val})/N=L*t := by
    dsimp [L,t]
    field_simp
  have hb := hblock S hS σ C k hk d U v t N ht hN
  rw [he] at hb
  apply hb.trans
  calc
    _≤K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+t)^(A+2)*
        (Ideal.absNorm C.val:ℝ)*N^2*((1+t)^A*min 1 (L^A)) :=
      mul_le_mul_of_nonneg_left (min_product_amplification L t hL ht A) (by positivity)
    _=K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
        min 1 (L^A)*(1+t)^(-2:ℝ) := by
      rw [Real.rpow_neg htp.le,Real.rpow_two,pow_add]
      field_simp
    _=_ := rfl

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramFrequencyMass -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gramFrequency_image_sum (E : Finset GramFrequency) (f : O→ℝ) :
    (∑k∈E.image Subtype.val,f k)=∑k∈E,f k.val :=
  Finset.sum_image (fun _ _ _ _ h=>Subtype.val_injective h)

theorem canonical_nonexceptional_frequency_sum (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,¬ExceptionalFrequency S hS C k)→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*H*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_weighted A hA a₀ b₀ ha₀ hab
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.frequency_weighted_sum
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ C E hE d U v H N hH hN
  have hc := hcount (E.image Subtype.val) H hH (by
    intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
  rw [gramFrequency_image_sum] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
    min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)
  have hV : 0≤V := by dsimp [V];positivity
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) :=
      Finset.sum_le_sum (fun k hk=>hblock S hS σ C k (hE k hk) d U v H N hH hN)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*H) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

theorem canonical_exceptional_frequency_sum (a b M ε : ℝ) (ha : 0<a) (hb : 0≤b)
    (hM : 0≤M) (hε : 0<ε) :
    ∃H₀ : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤M)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,ExceptionalFrequency S hS C k)→
      ∀(d : O)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2*
          ((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val)^ε*H^(1/6:ℝ) := by
  obtain ⟨H₀,K,hK,hblock⟩ := canonical_trivial_block a b M ha hb hM 2
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.exceptional_frequency_weighted_sum ε hε
  refine ⟨H₀,K*L,mul_pos hK hL,?_⟩
  intro W hcompact hs hW U S hS σ C E hE d v H N hH hN
  have hc := hcount (exceptionalModulus S hS C) (exceptionalModulus_nonzero S hS C)
    (E.image Subtype.val) H hH
    (by intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
    (by intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact hE j hj)
  rw [gramFrequency_image_sum,exceptionalModulus_norm,Nat.cast_mul] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2
  have hV : 0≤V := by dsimp [V];positivity
  have hp (k : GramFrequency) :
      ‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := by
    have ht : 0≤(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H := by positivity
    have hb := hblock W hcompact hs hW U S hS σ C k d N _ v hN ht
    have hpos : 0<1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H := by positivity
    rw [Real.rpow_neg hpos.le,Real.rpow_two,←div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
    convert hb using 1 ; dsimp [V] ; ring
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) := Finset.sum_le_sum (fun k _=>hp k)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val)^ε*H^(1/6:ℝ)) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramPrefactor -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_prefactor (c d F P Y Q : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*c*(Y/(c*d))^2*(P/c)*min 1 ((F*c*(P/c)/(Y/(c*d)))^A)=
      (Q/Y)*P*(c^(-2:ℝ)*d^(-2:ℝ)*min 1 ((c*d/(Y/(F*P)))^A)) := by
  have he : F*c*(P/c)/(Y/(c*d))=c*d/(Y/(F*P)) := by field_simp
  rw [he,Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two,Real.rpow_two]
  field_simp

lemma exceptional_prefactor (c d F P Y Q ε : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) :
    (Q/Y^3)*c*(Y/(c*d))^2*(F*c)^ε*(P/c)^(1/6:ℝ)=
      (Q/Y)*F^ε*P^(1/6:ℝ)*(c^(-7/6+ε:ℝ)*d^(-2:ℝ)) := by
  rw [Real.mul_rpow hF.le hc.le,Real.div_rpow hP.le hc.le,
    show (-7/6+ε:ℝ)=ε+(-1)+(-(1/6)) by ring,
    Real.rpow_add hc,Real.rpow_add hc,Real.rpow_neg_one,
    Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two]
  field_simp

lemma supported_nonexceptional_prefactor (C D : SupportedIdeal) (F P Y Q : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((F*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)=
      (Q/Y)*P*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(F*P)))^A)) :=
  nonexceptional_prefactor _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY A

lemma supported_exceptional_prefactor (C D : SupportedIdeal) (F P Y Q ε : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*
      (F*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ)=
      (Q/Y)*F^ε*P^(1/6:ℝ)*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) :=
  exceptional_prefactor _ _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramIdealMass -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma normalized_double_sum_bound (F G : Finset SupportedIdeal) (α V : SupportedIdeal→SupportedIdeal→ℂ)
    (hα : ∀C∈F,∀D∈G,‖α C D‖≤1) (p : ℝ) (hp : 0≤p) :
    ‖(p:ℂ)*(∑C∈F,∑D∈G,α C D*V C D)‖≤∑C∈F,∑D∈G,p*‖V C D‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  calc
    _≤p*(∑C∈F,∑D∈G,‖α C D*V C D‖) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _=>norm_sum_le _ _))) hp
    _≤p*(∑C∈F,∑D∈G,‖V C D‖) := by
      apply mul_le_mul_of_nonneg_left _ hp
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hα C hC D hD) (norm_nonneg _)).trans_eq (one_mul _)
    _=_ := by simp only [Finset.mul_sum]

theorem canonical_nonexceptional_ideal_sum (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (A : ℕ) (hA : 2<A) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a b)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,¬ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*P))^(-1+δ) := by
  obtain ⟨J,H₀,hfreq⟩ := canonical_nonexceptional_frequency_sum A hA a b ha hab
  obtain ⟨L,hL,hideal⟩ := gram_supported_double_sum δ hδ hδ1
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hfreq⟩ := hfreq W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) U v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
        min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)) := by ring
      _=_ := by rw [supported_nonexceptional_prefactor C D M P Y Q hM hP hY A];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by simp only [Finset.mul_sum]
    _≤B*(L*(Y/(M*P))^(-1+δ)) := mul_le_mul_of_nonneg_left (hideal A (by omega) _ (by positivity) F G) hB
    _=_ := by dsimp [B,M];ring

theorem canonical_exceptional_ideal_sum (ε : ℝ) (hε : 0<ε) (hε1 : ε<1/6)
    (a b M₀ : ℝ) (ha : 0<a) (hb : 0≤b) (hM₀ : 0≤M₀) :
    ∃H₀ : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤M₀)→
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*P^(1/6:ℝ) := by
  obtain ⟨H₀,K,hK,hfreq⟩ := canonical_exceptional_frequency_sum a b M₀ ε ha hb hM₀ hε
  obtain ⟨L,hL,hideal⟩ := gram_supported_exceptional_sum ε hε.le hε1
  refine ⟨H₀,K*L,mul_pos hK hL,?_⟩
  intro W hcompact hs hW S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*M^ε*P^(1/6:ℝ)
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq W hcompact hs hW U S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(M*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(M*gramIdealNorm C)^ε*(P/gramIdealNorm C)^(1/6:ℝ)) := by ring
      _=_ := by rw [supported_exceptional_prefactor C D M P Y Q ε hM hP hY];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) :=
      Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C^(-7/6+ε:ℝ)*gramIdealNorm D^(-2:ℝ)) := by simp only [Finset.mul_sum]
    _≤B*L := mul_le_mul_of_nonneg_left (hideal F G) hB
    _=_ := by dsimp [B,M];ring

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GramWindowGcd -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss

lemma commonColumns_window (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) :
    commonColumns (lowGaussColumns W hW Y hY) C=
      lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY) := by
  ext I
  rw [commonColumns_mem,lowGaussColumns_mem,lowGaussColumns_mem,common_column_ratio]

theorem original_window_gcd (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,f I J)=
      ∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑I∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        ∑J∈lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY),
        if IsCoprime I.val J.val then f (supportedIdealProduct C I) (supportedIdealProduct C J) else 0 := by
  rw [finite_pair_gcd]
  simp_rw [commonColumns_window]

lemma commonPool_norm_bound (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b)
    (C : SupportedIdeal) (hC : C∈commonPool (lowGaussColumns W hW Y hY)) :
    (Ideal.absNorm C.val:ℝ)≤b*Y := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hC
  have hnp : (Ideal.absNorm p.1.val:ℝ)≤b*Y :=
    (div_le_iff₀ hY).mp (hs ((lowGaussColumns_mem W hW Y hY p.1).mp (Finset.mem_product.mp hp).1)).2
  have hg : Ideal.absNorm (gcdCommon p.1 p.2).val≤Ideal.absNorm p.1.val :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.1.property.1))
      (map_dvd Ideal.absNorm (gcd_dvd_left p.1.val p.2.val))
  exact (by exact_mod_cast hg : (Ideal.absNorm (gcdCommon p.1 p.2).val:ℝ)≤Ideal.absNorm p.1.val).trans hnp

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass -/

section

namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma calibration_elementNorm_ge_one (C : CalibrationData) : 1≤elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma sexticGauss_norm_le (s : O) (hs : s≠0) (m : O) : ‖sexticGauss s hs m‖≤elementNorm s := by
  let := finite_quotient_span hs
  let : Fintype (O⧸Ideal.span {s}) := Fintype.ofFinite _
  rw [sexticGauss,tsum_fintype]
  calc
    _ ≤ ∑d : O⧸Ideal.span {s},‖idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s})*
      quotientTrace s hs (Ideal.Quotient.mk _ m*d)‖ := norm_sum_le _ _
    _ ≤ ∑_d : O⧸Ideal.span {s},(1:ℝ) := Finset.sum_le_sum (fun d _=>by
      rw [norm_mul,(quotientTrace s hs).norm_apply,mul_one]
      exact idealRowHom_norm _ _)
    _ = _ := by simp [elementNorm,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma physicalRowWeight_arithmetic_form (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*lowArithmeticCoefficient C r.1*
        (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
        C.residueMonoid r.2*(Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)) := by
  unfold physicalRowWeight lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma physicalRowWeight_crude_point (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (B0 B1 : ℝ) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : ∀x,‖W0 x‖≤B0) (hW1 : ∀x,‖W1 x‖≤B1)
    (X Y : ℝ) (hX : 1≤X) (hY : 0<Y) (r : PhysicalRowIndex) :
    ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1*‖C.tau‖⁻¹/Y := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hb := calibration_elementNorm_ge_one C
  have hscale : 0<elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X :=
    physicalRowScale_pos C X (lt_of_lt_of_le zero_lt_one hX) r.1
  have hqscale : (Ideal.absNorm r.1.val:ℝ)≤elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X := by
    have hbx : 1≤elementNorm C.generator*X := one_le_mul_of_one_le_of_one_le hb hX
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hqscale
  have hrad : (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)≤1 := by
    have hspos : 0<Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
      Real.sqrt (Ideal.absNorm r.1.val:ℝ) := mul_pos (Real.sqrt_pos.mpr hscale) (Real.sqrt_pos.mpr hq)
    calc
      _ = (Ideal.absNorm r.1.val:ℝ)/(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
        Real.sqrt (Ideal.absNorm r.1.val:ℝ)) := by simp only [div_eq_mul_inv,mul_inv_rev];ring
      _ ≤ 1 := (div_le_one hspos).mpr (by nlinarith [mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (Ideal.absNorm r.1.val:ℝ)), Real.sq_sqrt hq.le])
  have hg := sexticGauss_norm_le (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)
  have he := (primaryGenerator_spec r.1.val (supported_primaryGenerator_ne_zero r.1.val r.1.property)).1
  unfold elementNorm at hg
  rw [he] at hg
  rw [physicalRowWeight_arithmetic_form]
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Y⁻¹*B1*‖C.tau‖⁻¹*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      1*(Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)*B0 := by
      gcongr
      · exact hW1 _
      · exact lowArithmeticCoefficient_norm C r.1
      · exact C.residueMonoid_norm_le_one r.2
      · exact hW0 _
    _ = (B0*B1*‖C.tau‖⁻¹/Y)*((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
        (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hrad

lemma lowNumeratorRows_card (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 1≤Q) :
    ((lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)).card:ℝ)≤256*max 1 b*Q := by
  have hscale : 1≤2*max 1 b*Q := by nlinarith [le_max_left 1 b]
  have hh := DescentFiberCost.finite_element_count_real (lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)) _ hscale
    (by
      intro m hm
      have h := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ) m).mp hm)).2
      have hn := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hQ)).mp h
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      change elementNorm m≤2*max 1 b*Q
      exact hn.trans (by gcongr;exact le_max_right _ _))
  convert hh using 1 ; ring

lemma lowPhysicalScale_ge_one (C : CalibrationData) (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    1≤lowPhysicalScale C X Y :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (calibration_elementNorm_ge_one C) hX) hY

lemma physicalRowWeight_source_rectangle (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW1c : HasCompactSupport W1) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex)
    (hr : r∉(lowGaussColumns W1 hW1c Y hY) ×ˢ
      (lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY))) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  by_cases hs : r.1∈lowGaussColumns W1 hW1c Y hY
  · have hm : r.2∉lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY) := fun hm=>hr (Finset.mem_product.mpr ⟨hs,hm⟩)
    have hz : lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      simpa only [lowNumeratorRows_mem,not_not] using hm
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    change lowOuterCutoff _ _ (elementNorm r.2/lowPhysicalScale C X Y)*_=0
    rw [hz,zero_mul]
  · apply physicalRowWeight_outer_zero
    simpa only [lowGaussColumns_mem,not_not] using hs

theorem physicalRowWeight_source_mass (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀X Y : ℝ,1≤X → 1≤Y →
      (∑'r : PhysicalRowIndex,‖physicalRowWeight (calibrationForSet S hS) W0 W1 X Y r‖)≤
        K*lowPhysicalScale (calibrationForSet S hS) X Y := by
  let K := 32768*max 1 b1*max 1 (b0*b1)*B0*B1+1
  refine ⟨K,by dsimp only [K];positivity,?_⟩
  intro S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 X Y hX hY
  let C := calibrationForSet S hS
  have hx : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let Q := lowPhysicalScale C X Y
  have hQ : 1≤Q := lowPhysicalScale_ge_one C X Y hX hY
  let F := lowGaussColumns W1 hW1c Y hy
  let R := lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q (lowPhysicalScale_pos C X Y hx hy)
  have hzero (r : PhysicalRowIndex) (hr : r∉F×ˢR) : ‖physicalRowWeight C W0 W1 X Y r‖=0 := by
    rw [physicalRowWeight_source_rectangle C W0 W1 hW1c a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hx hy r hr,norm_zero]
  have hpoint (r : PhysicalRowIndex) : ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1/Y := by
    have h := physicalRowWeight_crude_point C W0 W1 B0 B1 hB0 hB1 hWB0 hWB1 X Y hX hy r
    simpa only [C,calibrationForSet_tau_norm,inv_one,mul_one] using h
  have hF : (F.card:ℝ)≤128*max 1 b1*Y := lowGaussColumns_card W1 hW1c Y hY a1 b1 hW1
  have hR : (R.card:ℝ)≤256*max 1 (b0*b1)*Q := by
    simpa only [R,max_eq_right (le_max_left 1 (b0*b1))] using lowNumeratorRows_card (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q hQ
  rw [tsum_eq_sum (s:=F×ˢR) hzero]
  calc
    _ ≤ ∑_r∈F×ˢR,B0*B1/Y := Finset.sum_le_sum (fun r _=>hpoint r)
    _ = (F.card:ℝ)*(R.card:ℝ)*(B0*B1/Y) := by simp [Finset.card_product,mul_assoc]
    _ ≤ (128*max 1 b1*Y)*(256*max 1 (b0*b1)*Q)*(B0*B1/Y) := by gcongr
    _ = (32768*max 1 b1*max 1 (b0*b1)*B0*B1)*Q := by field_simp;ring
    _ ≤ K*Q := mul_le_mul_of_nonneg_right (by dsimp only [K];linarith) (le_trans zero_le_one hQ)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalMass -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalScaleMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*lowPhysicalScale C (X k) (Y k)

theorem gaussianPhysicalFamily_mass_bound (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      gaussianPhysicalFamilyMass (calibrationForSet S hS) W0 W1 F a X Y W q≤
        K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q := by
  obtain ⟨K,hK,hb⟩ := physicalRowWeight_source_mass a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨K,hK,?_⟩
  intro α ι _ S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  unfold gaussianPhysicalFamilyMass gaussianPhysicalScaleMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ (‖a k‖*(∏i,‖W i (q k i)‖))*(K*lowPhysicalScale (calibrationForSet S hS) (X k) (Y k)) :=
      mul_le_mul_of_nonneg_left (hb S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 (X k) (Y k) (hX k hk) (hY k hk)) (by positivity)
    _ = _ := by ring

theorem gaussianPhysicalFamily_remote_polynomial (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ)
    (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,HasCompactSupport W0→HasCompactSupport W1→
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hremote⟩ := gaussianPhysicalFamily_remote V hV N
  obtain ⟨C1,hC1,hmass⟩ := gaussianPhysicalFamily_mass_bound a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro α ι _ η S hS W0 W1 hW0c hW1c hW0 hW1 hWB0 hWB1 F a D X Y hX hY W q Z A hZ hA
  have hh := hremote η (calibrationForSet S hS) W0 W1 hW0c hW1c F a D X Y
    (fun k hk=>lt_of_lt_of_le zero_lt_one (hX k hk)) (fun k hk=>lt_of_lt_of_le zero_lt_one (hY k hk)) W q Z A hZ hA
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := hmass S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  calc
    _ ≤ C0*(C1*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q)*Z^2/A^N := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RestrictedEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRestrictedEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm
open CenteredMomentPlainEnergy CenteredMomentPlainChildEnergy CenteredMomentCauchy CenteredMomentSmooth
open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def restrictedEnergy {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (c : α → ℂ) (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0

theorem restricted_summable {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => if keep z then
      ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c W K hK).hasSum
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  exact hs.summable.indicator {z | keep z}

theorem finite_energy_le_restricted {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep z)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c z‖^2) ≤ restrictedEnergy keep S a c W K := by
  calc
    _ ≤ ∑ z ∈ rows, if keep z then
        ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re else 0 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [ite_eq_left (hkeep z hz)]
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows
      (by intro z hz; split_ifs; exact mul_nonneg (sq_nonneg _) (hW z); exact le_rfl)
      (restricted_summable keep S a ha c W K hK).hasSum

theorem finite_negative_energy_le_restricted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hkeep : ∀ z ∈ rows, keep (-z))
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c (-z)‖^2) ≤ restrictedEnergy keep S a c W K := by
  have he := finite_energy_le_restricted keep S a ha c W K hK (rows.image Neg.neg)
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz; exact hkeep w hw) hW
    (by intro z hz; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rwa [Finset.sum_image (fun x hx y hy hxy => neg_injective hxy)] at he

def nonexceptional (η : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A₀ z : O) : Prop :=
  z ≠ 0 ∧ ¬CenteredExceptionalProfile.FixedInducingRow
    (CenteredMomentChildRows.childCharacter η χ) Q m A₀ z

theorem nonexceptional_reflection (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ (-z) := by
  unfold nonexceptional
  rw [neg_ne_zero]
  exact and_congr Iff.rfl (CenteredMomentExceptionalReflection.not_fixedInducingRow_reflection_iff
    η χ ξ Q hQ m A₀ z hmLam hm2)

theorem nonexceptional_ray_independent (η : HeckeFamily.Character)
    (χ ξ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    nonexceptional η χ Q m A₀ z ↔ nonexceptional η ξ Q m A₀ z := by
  have h₁ := nonexceptional_reflection η χ ξ Q hQ m A₀ z hmLam hm2
  have h₂ := nonexceptional_reflection η ξ ξ Q hQ m A₀ (-z) hmLam hm2
  simpa only [neg_neg] using h₁.trans h₂

theorem whole_kernel_restricted_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ) (keep₁ keep₂ : O → Prop),
      (∀ z ∈ rows, keep₁ z) → (∀ z ∈ rows, keep₂ (-z)) →
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (restrictedEnergy keep₁ S a (fun i => c i * columnPhase (V 2) (u i) t) U K) ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (restrictedEnergy keep₂ T b (fun j => d j * star (columnPhase (V 3) (v j) t)) U K) ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η keep₁ keep₂ hkeep₁ hkeep₂ hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * idealRowHom z (Ideal.span {a i}))
    (fun z j => d j * idealRowHom (-z) (Ideal.span {b j})) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_restricted keep₁ S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hkeep₁ hU hmajor).trans (hleft t)
  have hR' := (finite_negative_energy_le_restricted keep₂ T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hkeep₂ hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial S a (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial T b (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_rowPolynomial, rightColumn_eq_star_rowPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentRestrictedEnergy

end

end OAI

end

