module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part025
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part023
public import Green64.Library.Analysis.NumberTheory.DirichletL.Dictionary.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part018
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part026

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedRetainedRadius
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O

theorem ballProfile_support_upper (x : ℝ) (hx : 0≤x) (h : ballProfile x≠0) : x<2 := by
  have hb : x∈Function.support QuadraticInitialBound.sieveBump := by
    intro hz
    exact h (by simp only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,hz,Complex.ofReal_zero])
  rw [QuadraticInitialBound.sieveBump.support_eq] at hb
  simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hx,
    QuadraticInitialBound.sieveBump] using hb

theorem ballProfile_radius_le (x Y V : ℝ) (hx : 0≤x) (hY : 0<Y) (hV : 0<V)
    (hscale : 2*Y≤V) : (ballProfile (x/Y)).re≤(ballProfile (x/V)).re := by
  by_cases hz : ballProfile (x/Y)=0
  · simpa only [hz,Complex.zero_re] using ballProfile_nonneg (x/V)
  have hs := ballProfile_support_upper (x/Y) (div_nonneg hx hY.le) hz
  have hxy : x≤V := ((div_lt_iff₀ hY).mp hs).le.trans hscale
  rw [ballProfile_one (x/V) (div_nonneg hx hV.le) ((div_le_one hV).mpr hxy)]
  exact ballProfile_le_one _

theorem gaussEnergy_radius_le {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (Y V : ℝ) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    (gaussEnergy S a ha c ballProfile Y).re≤(gaussEnergy S a ha c ballProfile V).re := by
  have h1 := gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  have h2 := gaussEnergy_hasSum_re S a ha c ballProfile V hV
  rw [←h1.tsum_eq,←h2.tsum_eq]
  apply Summable.tsum_le_tsum _ h1.summable h2.summable
  intro z
  exact mul_le_mul_of_nonneg_left
    (ballProfile_radius_le _ Y V (sq_nonneg _) hY hV hscale) (sq_nonneg _)

theorem sourceGaussEnergy_radius_le (Q : Finset (Ideal O)) (c f : Ideal O→ℂ)
    (Y V : ℝ) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    (sourceGaussEnergy Q c f ballProfile Y).re≤(sourceGaussEnergy Q c f ballProfile V).re :=
  gaussEnergy_radius_le _ _ _ _ Y V hY hV hscale

theorem childEnergy_radius_le {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→Character) (p : O) (n : ℕ)
    (t T Y V : ℝ) (hT : 0≤T) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    D.childEnergy τ p n t T Y≤D.childEnergy τ p n t T V := by
  unfold OriginalData.childEnergy
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_le_div_of_nonneg_right _ (div_nonneg hT (by positivity))
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum
  intro B _
  exact sourceGaussEnergy_radius_le _ _ _ Y V hY hV hscale

lemma exponent_max (d K0 j c g : ℝ) :
    j+(max (d+K0-j-c) 0+g)=max (j+g) (d+K0-c+g) := by
  by_cases h : d+K0-j-c≤0
  · rw [max_eq_right h,max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_right (by linarith)]
    ring

lemma rpow_exponent_max (Z a b : ℝ) (hZ : 1≤Z) :
    Z^(max a b)=max (Z^a) (Z^b) := by
  rcases le_total a b with h|h
  · rw [max_eq_right h,max_eq_right (Real.rpow_le_rpow_of_exponent_le hZ h)]
  · rw [max_eq_left h,max_eq_left (Real.rpow_le_rpow_of_exponent_le hZ h)]

theorem main_radius_identity (Z d K0 j c sigma : ℝ) (hZ : 1≤Z) :
    Z^(j+mainGain (d+K0-j) c sigma)=
      max (Z^(j+2*sigma)) (Z^(d+K0-c+2*sigma)) := by
  rw [mainGain,exponent_max,rpow_exponent_max Z _ _ hZ]

theorem error_radius_identity (Z d K0 j c sigma : ℝ) (p : O) (k : ℕ) (hZ : 1≤Z) :
    Z^(j+errorGain (d+K0-j) c sigma Z p k)=
      max (Z^(j+sigma))
        (Z^(d+K0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma)) := by
  have he := exponent_max d K0 j (c+2*errorRemoval p Z k-errorMoving p Z k) sigma
  have hbase : j+errorGain (d+K0-j) c sigma Z p k=
      max (j+sigma) (d+K0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma) := by
    unfold errorGain
    convert he using 1 <;> ring_nf
  rw [hbase,rpow_exponent_max Z _ _ hZ]

lemma envelope_exponent (d K0 j c g δ : ℝ) (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+(max (d+K0-j-c) 0+g)≤K0+max (d-c) 0+g+δ := by
  rw [exponent_max]
  apply max_le
  · linarith [le_max_right (d-c) (0:ℝ)]
  · linarith [le_max_left (d-c) (0:ℝ)]

theorem main_exponent_envelope (d K0 j c sigma δ : ℝ) (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+mainGain (d+K0-j) c sigma≤K0+max (d-c) 0+2*sigma+δ :=
  envelope_exponent d K0 j c (2*sigma) δ hδ hj

theorem error_exponent_envelope (d K0 j c sigma δ Z : ℝ) (p : O) (k : ℕ)
    (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+errorGain (d+K0-j) c sigma Z p k≤
      K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ := by
  have he := envelope_exponent d K0 j (c+2*errorRemoval p Z k-errorMoving p Z k) sigma δ hδ hj
  unfold errorGain
  convert he using 1 <;> ring_nf

theorem eventually_support_reserve (reserve : ℝ) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ 2≤Z^reserve := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hreserve).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

lemma doubled_radius_le (Z a b reserve : ℝ) (hZ : 1<Z) (hab : a≤b)
    (hreserve : 2≤Z^reserve) : 2*Z^a≤Z^(b+reserve) := by
  rw [Real.rpow_add (zero_lt_one.trans hZ)]
  calc
    _≤2*Z^b := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hab) (by norm_num)
    _≤Z^b*Z^reserve := by
      rw [mul_comm (Z^b)]
      exact mul_le_mul_of_nonneg_right hreserve (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

theorem unamplified_radius_identity (Z d K0 j c sigma : ℝ) (hZ : 1≤Z) :
    Z^(j+(max (d+K0-j-c) 0+sigma))=
      max (Z^(j+sigma)) (Z^(d+K0-c+sigma)) := by
  rw [exponent_max,rpow_exponent_max Z _ _ hZ]

theorem dyadic_to_common_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
    (Z d K0 c sigma δ reserve : ℝ) (hZ : 1<Z) (hsigma : 0≤ sigma) (hδ : 0≤δ)
    (n : ℤ) (hn : Real.logb Z (dyadicScale n)≤K0+δ) (hreserve : 2≤Z^reserve) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha coeff h‖^2)≤
      (gaussEnergy S a ha coeff ballProfile (Z^(K0+max (d-c) 0+sigma+δ+reserve))).re := by
  apply (dyadic_to_ball S a ha coeff Z sigma
    (d+K0-Real.logb Z (dyadicScale n)) c hZ hsigma n).trans
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (envelope_exponent d K0 _ c sigma δ hδ hn) hreserve

def mainCommonRadius (Z d K0 c sigma δ reserve : ℝ) : ℝ :=
  Z^(K0+max (d-c) 0+2*sigma+δ+reserve)

def errorCommonRadius (Z d K0 c sigma δ reserve : ℝ) (p : O) (k : ℕ) : ℝ :=
  Z^(K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ+reserve)

theorem main_energy_common {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
    (Z d K0 j c sigma δ reserve : ℝ) (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    (gaussEnergy S a ha coeff ballProfile (Z^(j+mainGain (d+K0-j) c sigma))).re≤
      (gaussEnergy S a ha coeff ballProfile (mainCommonRadius Z d K0 c sigma δ reserve)).re := by
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (main_exponent_envelope d K0 j c sigma δ hδ hj) hreserve

theorem child_energy_common {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→Character) (p : O) (n : ℕ)
    (t T Z d K0 j c sigma δ reserve : ℝ) (hT : 0≤T) (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    D.childEnergy τ p n t T (Z^(j+errorGain (d+K0-j) c sigma Z p (n+1)))≤
      D.childEnergy τ p n t T (errorCommonRadius Z d K0 c sigma δ reserve p (n+1)) := by
  apply childEnergy_radius_le D τ p n t T _ _ hT
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (error_exponent_envelope d K0 j c sigma δ Z p (n+1) hδ hj) hreserve

theorem errorCommonRadius_six (Z d K0 c sigma δ reserve : ℝ) (p : O) :
    errorCommonRadius Z d K0 c sigma δ reserve p 6=
      Z^(K0+max (d-c-2*errorRemoval p Z 6) 0+sigma+δ+reserve) := by
  simp only [errorCommonRadius,errorMoving,ite_true,add_zero]

open CenteredMomentFirstScale

theorem retained_nominal_upper (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    Real.logb Z (dyadicScale n)≤nominalLog I J E K X Z+frequencyLoss Z Csec xi := by
  apply retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC _ n hn
  rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (firstNominalScale_pos I J E hE K X hK hX)]
  exact hsec

theorem actual_retained_radii (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (hreserve : 2≤Z^reserve) :
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let δ := frequencyLoss Z Csec xi
    2*Z^(j+mainGain (d+K0-j) c sigma)≤ mainCommonRadius Z d K0 c sigma δ reserve ∧
      ∀(p:O)(k:ℕ),2*Z^(j+errorGain (d+K0-j) c sigma Z p k)≤
        errorCommonRadius Z d K0 c sigma δ reserve p k := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  constructor
  · exact doubled_radius_le Z _ _ reserve hZ (main_exponent_envelope _ _ _ _ _ _ hδ hj) hreserve
  · intro p k
    exact doubled_radius_le Z _ _ reserve hZ (error_exponent_envelope _ _ _ _ _ _ Z p k hδ hj) hreserve

open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationGlobal

theorem eventually_original_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          HeckeRowClosure.rowConductorBound (CenteredMomentChildRows.childCharacter η χ) m 1 (p.val^(2*CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (j : ℤ),Retained (frequencyRadius Tsec Z xi) j →
          Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve p (errorIndex i+1))) := by
  filter_upwards [eventually_original_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap,
    eventually_support_reserve reserve hreserve] with Z hz hsupport
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec j hj hMdyad
  let K0 := nominalLog I J E K X Z
  let kdyad := Real.logb Z (dyadicScale j)
  have henclose : kdyad≤K0+frequencyLoss Z Csec xi :=
    retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
      (zero_lt_one.trans_le hC) hsec j hj
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have he := henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T
    (d+K0-kdyad) cLog hT j hMdyad
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact main_energy_common _ _ _ _ Z d K0 kdyad cLog sigma _ reserve hZ hδ henclose hsupport.2
  · apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    exact child_energy_common D.active (τ p i) p (errorIndex i) t T Z d K0 kdyad cLog sigma
      _ reserve hT.le hZ hδ henclose hsupport.2

end SevenEighths.CenteredMomentAmplifiedRetainedRadius

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalChoice -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentAmplificationRadicalChoice
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem exists_pool_error_families {ι : Type*} [Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : Character) (m : O) (hm : m≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ p∈elementPool P,∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤ sigma → ∀ (j : ℤ),
        (∑p∈elementPool P,∑h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
            (D.coefficient η m t T) h p)≤
        ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
          (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1))) := by
  have hf (p : elementPool P) (i : Fin 3) := by
    have hd := elementPool_data P hP hbad p p.property
    have hPid := hP _ hd.2.1
    letI : (Ideal.span {p.val}).IsMaximal :=
      (Ideal.isPrime_of_prime hPid).isMaximal hPid.ne_zero
    exact CenteredMomentAmplificationRadicalFamily.exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hmLam hm2 (errorIndex i) (errorIndex_cases i)
  choose τ hτ using hf
  refine ⟨τ,fun p i => (hτ p i).1,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  rw [←Finset.sum_coe_sort (elementPool P)]
  apply Finset.sum_le_sum
  intro p hp
  have h0 := (hτ p 0).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h5 := (hτ p 1).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h6 := (hτ p 2).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  simpa only [errorEnergy,Finset.sum_add_distrib,Fin.sum_univ_three,
    show errorIndex 0=0 from rfl,show errorIndex 1=5 from rfl,show errorIndex 2=6 from rfl,Nat.reduceAdd] using
    add_le_add (add_le_add h0 h5) h6

theorem eventually_original_source_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,∀ I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_dyadic_amplification M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,herr⟩ := exists_pool_error_families (ι:=ι) _
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1) η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have hcop (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
      ∀i,∀I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I := by
    have hd := elementPool_data _ (fun Q hQ => (hdata Q hQ).1)
      (fun Q hQ => (hdata Q hQ).2.1) p hp
    exact original_slot_coprime D Z sigma b eta hZ.le hb hsep z hz hlen hsupp hslot hprime
      (Ideal.span {p}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  have he := herr D hS hprime hcop t T Z sigma D0 cLog hT hZ hsigma.le j
  apply (hamp Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) D.R D.s hR0 hs0 hR hs j hK D0 cLog).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by positivity)

theorem eventually_original_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_original_source_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have he := henergy D.active (fun i I hI => hS i I (D.active_subset i hI))
    (fun i I hI => hprime i I (D.active_subset _ hI)) D.active_slot hsupp z hz hlen
    hR0 hs0 hR hs t T D0 cLog hT j hK
  simpa only [D.active_gaussPolynomial,D.active_gaussEnergy] using he

theorem eventually_original_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (j : ℤ),Retained (frequencyRadius Tsec Z xi) j →
          Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve p (errorIndex i+1))) := by
  filter_upwards [eventually_original_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap,
    eventually_support_reserve reserve hreserve] with Z hz hsupport
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec j hj hMdyad
  let K0 := nominalLog I J E K X Z
  let kdyad := Real.logb Z (dyadicScale j)
  have henclose : kdyad≤K0+frequencyLoss Z Csec xi :=
    retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
      (zero_lt_one.trans_le hC) hsec j hj
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have he := henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T
    (d+K0-kdyad) cLog hT j hMdyad
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact main_energy_common _ _ _ _ Z d K0 kdyad cLog sigma _ reserve hZ hδ henclose hsupport.2
  · apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    exact child_energy_common D.active (τ p i) p (errorIndex i) t T Z d K0 kdyad cLog sigma
      _ reserve hT.le hZ hδ henclose hsupport.2

end SevenEighths.CenteredMomentAmplificationRadicalChoice

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonRadiusSaving -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadiusSaving
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem common_saving_identity (c d x w q wo B sigma branch delta reserve ell : ℝ) :
    firstSaving c (d+x) w q wo B
      (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell =
      c/6+5*d/6+w/3+q/6+wo+B-5*max (d-c-2*w+wo) 0/6-
        5*branch*sigma/6-5*(delta+reserve)/6+ell := by
  unfold firstSaving
  ring

theorem common_saving_lower (c d x w q wo B sigma branch delta reserve ell : ℝ)
    (hc : 0≤ c) (hw : 0≤w) (hq : 0≤q) (hwo : 0≤wo) (hB : 0≤B)
    (hallow : 3*c-5*d≤6*B+q) :
    2*(c+w)/3-max (w/3-wo) 0-5*branch*sigma/6-5*(delta+reserve)/6+ell≤
      firstSaving c (d+x) w q wo B
        (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell := by
  rw [common_saving_identity]
  have hm0 := le_max_right (w/3-wo) (0:ℝ)
  have hm1 := le_max_left (w/3-wo) (0:ℝ)
  by_cases h : 0≤d-c-2*w+wo
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem main_saving_lower (c d x q B sigma delta reserve : ℝ)
    (hc : 0≤ c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q) :
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+x) 0 q 0 B
        (x+max (d-c) 0+2*sigma+delta+reserve) (sigma/3) := by
  have hh := common_saving_lower c d x 0 q 0 B sigma 2 delta reserve (sigma/3)
    hc (by norm_num) hq (by norm_num) hB hallow
  norm_num only [zero_div,sub_zero,add_zero,mul_zero,max_self] at hh
  linarith

theorem error_penalty_le (l sigma : ℝ) (hl : 0≤l) (hu : l≤ sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0≤2*sigma/3 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [Nat.cast_ofNat,ite_false,ite_true,
    one_mul,sub_zero] <;> apply max_le <;> linarith

def errorLoss (sigma : ℝ) (k : ℕ) : ℝ :=
  if k=1 then 5*sigma/6 else if k=6 then 3*sigma/2 else 23*sigma/18

theorem error_penalty_refined (l sigma : ℝ) (hl : 0≤l) (hu : l≤ sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0+5*sigma/6≤errorLoss sigma k := by
  have hs : 0≤ sigma := by linarith
  rcases hk with rfl|rfl|rfl
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_one,one_mul]
    have hm : max (l/3-l) 0=0 := max_eq_right (by linarith)
    rw [hm,zero_add]
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat,sub_zero]
    have hm : max (6*l/3) 0≤2*sigma/3 := max_le (by linarith) (by linarith)
    linarith
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat]
    have hm : max (7*l/3-l) 0≤4*sigma/9 := max_le (by linarith) (by linarith)
    linarith

theorem errorLoss_le (sigma : ℝ) (hs : 0≤ sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7) : errorLoss sigma k≤3*sigma/2 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [errorLoss,ite_true,ite_false] <;> linarith

theorem error_saving_refined (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤ c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤ sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_refined l sigma hl hu k hk]

theorem error_saving_lower (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤ c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤ sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_le l sigma hl hu k hk]

theorem common_gain_width (d x c w wo sigma delta reserve branch : ℝ)
    (hs : 0≤ sigma) (hd : 0≤delta) (hr : 0≤ reserve) (hb : 1≤branch)
    (hx : -delta≤x) :
    0≤x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve ∧
    (d+x)-c-2*w+wo+sigma≤
      x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve := by
  have h0 := le_max_right (d-c-2*w+wo) (0:ℝ)
  have h1 := le_max_left (d-c-2*w+wo) (0:ℝ)
  constructor <;> nlinarith

theorem saving_power_factor (Z F c w sigma delta reserve : ℝ) (hZ : 1≤Z)
    (hF : 2*(c+w)/3-3*sigma/2-5*(delta+reserve)/6≤F) :
    Z^(-F)≤Z^(-2*(c+w)/3+3*sigma/2+5*(delta+reserve)/6) := by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  linarith

theorem main_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j=
      (K0-j)+max (d-c) 0+2*sigma+delta+reserve := by
  rw [mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem error_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z)
    (p : O) (k : ℕ) :
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j=
      (K0-j)+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        sigma+delta+reserve := by
  rw [errorCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem canonical_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    let B := c+d-2*p-R
    0≤ c ∧ 0≤q ∧ 0≤B ∧ 3*c-5*d≤6*B+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hh := actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at hh
  have hc : 0≤Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have h0 := le_max_right (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h1 := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h2 := le_max_right (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  exact ⟨hc,hq.1,by linarith,by linarith [hq.2]⟩

theorem actual_main_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_error_common_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_main_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z) (hs : 0≤ sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))≤
      Z^(-2*c/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_main_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)≤
      Z^(-2*(c+errorRemoval p0 Z k)/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_error_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve
    hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

open CenteredMomentFirstScale

theorem actual_common_radius_widths (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec)
    (hxi : 0≤xi) (hs : 0≤ sigma) (hr : 0≤ reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let delta := frequencyLoss Z Csec xi
    let gm := Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j
    (0≤gm ∧ d+K0-j-c+sigma≤gm) ∧
    ∀p : O,∀k : ℕ,
      let ge := Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j
      0≤ge ∧ d+K0-j-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤ge := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hd := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have hx : -frequencyLoss Z Csec xi≤nominalLog I J E K X Z-Real.logb Z (dyadicScale n) := by
    linarith
  constructor
  · rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) 0 0 sigma
      (frequencyLoss Z Csec xi) reserve 2 hs hd hr (by norm_num) hx
    simp only [mul_zero,sub_zero,add_zero] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩
  · intro p k
    rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
      sigma (frequencyLoss Z Csec xi) reserve 1 hs hd hr (by norm_num) hx
    simp only [one_mul] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩

end SevenEighths.CenteredMomentCommonRadiusSaving

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAnnularGeometry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentFirstAnnularGeometry
open CenteredMomentSectorLocalization CenteredMomentFirstAnnularMajorant
open CenteredMomentFirstAnnularEnergy CenteredMomentGaussEnergy CanonicalQuadraticSieve

local notation "O"=>HeckeFamily.O

lemma retained_of_scale_le (j:ℤ)(R:ℝ)(h:dyadicScale j≤R):Retained R j:=by
  refine ⟨dyadicScale j/2, by exact div_pos (dyadicScale_pos j) (by norm_num), by linarith [dyadicScale_pos j], ?_⟩
  apply subset_closure
  change dyadicWeight j (dyadicScale j/2)≠0
  have he:(dyadicScale j/2)/dyadicScale j=(1/2:ℝ):=by
    field_simp [ne_of_gt (dyadicScale_pos j)]
  rw [dyadicWeight,he,annulus,cutoff_one _ (by norm_num)]
  norm_num [cutoff_zero]

lemma bands_retained (H R:ℝ)(hH:0<H)(hR:8*H≤R)(j:ℤ)(hj:j∈bands H):
    Retained R j:=retained_of_scale_le j R ((bands_scale H hH j hj).2.trans hR)

lemma bands_log_cap (H Z A:ℝ)(hH:0<H)(hZ:1<Z)(hcap:8*H≤Z^A)
    (j:ℤ)(hj:j∈bands H):Real.logb Z (dyadicScale j)≤A:=by
  have he:Real.logb Z (Z^A)=A:=Real.logb_rpow (by positivity) (ne_of_gt hZ)
  rw [←he]
  exact Real.logb_le_logb_of_le hZ (dyadicScale_pos j) ((bands_scale H hH j hj).2.trans hcap)

lemma bands_nonempty (H:ℝ)(hH:0<H):(bands H).Nonempty:=by
  by_contra hn
  have he:bands H=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  have hp:=weighted_partition H (H/2) hH
  have hr:(H/2)/H=(1/2:ℝ):=by field_simp
  rw [hr,profile_one _ (by norm_num) (by norm_num),he] at hp
  norm_num at hp

theorem common_bound {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0<H)(hB:0≤B)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  apply (energy_le_dyadic S a ha c H hH).trans
  calc
    _≤∑j∈bands H,B:=Finset.sum_le_sum hb
    _=((bands H).card:ℝ)*B:=by simp
    _≤7*B:=mul_le_mul_of_nonneg_right (bands_card H hH) hB

theorem common_bound_auto {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(H B:ℝ)(hH:0<H)
    (hb:∀j∈bands H,(∑' z : O, dyadicWeight j (normValue z)*‖gaussPolynomial S a ha c z‖^2)≤B):
    (gaussEnergy S a ha c profile H).re≤7*B:=by
  obtain ⟨j,hj⟩:=bands_nonempty H hH
  have hB:0≤B:=(tsum_nonneg (fun z=>mul_nonneg (dyadicWeight_bounds j _).1 (sq_nonneg _))).trans (hb j hj)
  exact common_bound S a ha c H B hH hB hb

end SevenEighths.CenteredMomentFirstAnnularGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAnnularAmplification -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularAmplification
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem eventually_annular_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi →
          8*H0≤Z^Mmax →
          (gaussEnergy Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            CenteredMomentFirstAnnularMajorant.profile H0).re≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentAmplificationRadicalChoice.eventually_original_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta (32*Csec) xi reserve
    hsigma hloss hM hb hgap (by linarith) hxi hreserve] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩:=hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have hsec' :32*Tsec≤(32*Csec)*firstNominalScale I J E K X:=by nlinarith
  have hfreq:8*H0≤frequencyRadius (32*Tsec) Z xi:=by
    unfold frequencyRadius at houter ⊢
    nlinarith
  have hbnd:=CenteredMomentFirstAnnularGeometry.common_bound_auto Finset.univ
    (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) H0 _ hH0 (fun j hj=>
      henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
        I J E hE K X (32*Tsec) hK hX hsec' j
        (CenteredMomentFirstAnnularGeometry.bands_retained H0 _ hH0 hfreq j hj)
        (CenteredMomentFirstAnnularGeometry.bands_log_cap H0 Z Mmax hH0 hZ hcap j hj))
  convert hbnd using 1 ; ring

end SevenEighths.CenteredMomentFirstAnnularAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAnnularInput -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussNormalization
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum

variable {ι:Type*}[Fintype ι]

theorem normalized_input_coefficient (s:Input ι)(R seed:Ideal HeckeFamily.O)
    (W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original s R seed).columns)
      (sourceGenerator_supported (original s R seed).columns)
      ((original s R seed).coefficient s.η fixedBadMask s.t (volume s)) W H).re=
      normalizedGaussSource s R seed W H:=by
  unfold OriginalData.coefficient normalizedGaussSource sourceGaussEnergy
  rw [show (fun I:supportedColumns (original s R seed).columns=>
      (Real.sqrt (volume s):ℂ)⁻¹*((original s R seed).beta I*
        CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 s.t I))=
      (fun I:supportedColumns (original s R seed).columns=>(Real.sqrt (volume s):ℂ)⁻¹*
        ((original s R seed).beta I*heightCoeff s.η s.t I)) by
    funext I
    rw [←heightCoeff_eq_fixed_rowWeight s.η s.t I (Finset.mem_filter.mp I.property).2]]
  exact gaussEnergy_central _ _ _ _ (volume s) (volume_pos s) W H

theorem normalized_child_coefficient (s:Input ι)(C R seed:Ideal HeckeFamily.O)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(H:ℝ):
    (gaussEnergy Finset.univ (sourceGenerator (original (child s C R B τ t) (R*C) seed).columns)
      (sourceGenerator_supported (original (child s C R B τ t) (R*C) seed).columns)
      ((original (child s C R B τ t) (R*C) seed).coefficient τ fixedBadMask t
        (volume (child s C R B τ t))) W H).re=
      childNormalizedGaussSource s C R seed B τ t W H:=
  normalized_input_coefficient (child s C R B τ t) (R*C) seed W H

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily

variable {ι:Type*}[Fintype ι]

def activeInput (s:Input ι):Input ι:={s with
  slots:=fun i=>(s.slots i).filter (fun I=>s.W i ((I.absNorm:ℝ)/s.P i)≠0)
  prime:=fun i I hI=>s.prime i I (Finset.mem_filter.mp hI).1
  coefficient_bound:=fun i I hI=>s.coefficient_bound i I (Finset.mem_filter.mp hI).1}

lemma original_active (s:Input ι)(R seed:Ideal HeckeFamily.O):
    original (activeInput s) R seed=(original s R seed).active:=by
  unfold original OriginalData.active
  congr 1
  funext j
  cases j <;> rfl

lemma active_volume (s:Input ι):volume (activeInput s)=volume s:=rfl

lemma active_normalized (s:Input ι)(R seed:Ideal HeckeFamily.O)(W:𝓢(ℝ,ℂ))(H:ℝ):
    normalizedGaussSource (activeInput s) R seed W H=normalizedGaussSource s R seed W H:=by
  rw [←normalized_input_coefficient,←normalized_input_coefficient,original_active]
  exact congrArg Complex.re ((original s R seed).active_gaussEnergy s.η fixedBadMask s.t (volume s) W H)

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAnnularInputAmplification -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAnnularInput
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

theorem eventually_input_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                normalizedGaussSource s R seed ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z (32*Csec) xi) reserve)+
                ∑p : elementPool P,∑i : Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
                    ∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools
                        ((Ideal.span {p.val})^(errorIndex i+1)),
                      childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                        R seed B (τ p i χ) s.t ballProfile
                        (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                          (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))) := by
  filter_upwards [CenteredMomentFirstAnnularAmplification.eventually_annular_amplification_common
    (ι:=ι) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
    hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _)
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  have he:=henergy (original s R seed) s.pools_ne s.prime hsupp z hz hlen hR0 hs0 hR hs
    s.t (volume s) d cLog (volume_pos s) I J E hE K X Tsec hK hX hsec H0 hH0 houter hcap
  rw [←hsη,normalized_input_coefficient,normalized_input_coefficient] at he
  convert he using 1
  congr 2
  apply Finset.sum_congr rfl
  intro p _
  have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
    (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
  have hcop:∀i,∀Q∈(activeInput s).slots i,IsCoprime (Ideal.span {p.val}) Q:=by
    exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
      hsupp (original s R seed).active_slot
      (fun i Q hQ=>s.prime i Q ((original s R seed).active_subset _ hQ))
      (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  apply Finset.sum_congr rfl
  intro i _
  rw [←original_active]
  exact (original_childEnergy_eq_inputs (activeInput s) R seed (τ p i) p.val hd.1.ne_zero hcop
    (errorIndex i) s.t _).symm

end SevenEighths.CenteredMomentFirstAnnularInput

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstChildLower -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstChildLower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonExceptionalGates CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem child_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤ s.X₁)(hX₂:Z^r≤ s.X₂)(hY₁:Z^r≤ s.Y₁)(hY₂:Z^r≤ s.Y₂):
    let d:=child s C R B τ t
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₂ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₂:=by
  exact ⟨extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂,
    extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂⟩

theorem twice_lower (s:Input ι)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)
    (Q:Ideal O)(hQ:Q≠0)(k:ℕ)
    (Bp:actualAllocations (child s C R B τ t).pools (Q^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤ s.X₁)(hX₂:Z^r≤ s.X₂)(hY₁:Z^r≤ s.Y₁)(hY₂:Z^r≤ s.Y₂):
    let d:=twiceChild s C R B τ t Q k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-(k:ℝ)*Real.logb Z (Q.absNorm:ℝ)
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hp:=child_lower (child s C R B τ t) (Q^k) (R*C) (pow_ne_zero k hQ)
    Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hnorm:(Q.absNorm:ℝ)>0:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hQ)
  have he:Real.logb Z ((Q^k).absNorm:ℝ)=(k:ℝ)*Real.logb Z (Q.absNorm:ℝ):=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
  simpa only [he,twiceChild] using hp

theorem removed_width_cap (L c w:ℝ):
    (2/3:ℝ)*(c+w)+(2/3:ℝ)*max (L-c-w) 0≥(2/3:ℝ)*L:=by
  have h:=le_max_left (L-c-w) 0
  linarith

theorem paired_removed_width_cap (L c₁ w₁ c₂ w₂:ℝ):
    ((c₁+w₁)+(c₂+w₂))/3+
      (max (L-c₁-w₁) 0+max (L-c₂-w₂) 0)/3≥(2/3:ℝ)*L:=by
  have h₁:=le_max_left (L-c₁-w₁) 0
  have h₂:=le_max_left (L-c₂-w₂) 0
  linarith

end SevenEighths.CenteredMomentFirstChildLower

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFixedRowMask
open CenteredMomentFirstFamily CenteredMomentFirstIdealFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationFamily CenteredMomentSourceAllocationEnergy
open CenteredMomentAmplificationFamilyEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentPrimaryCharacter
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentChildAssembly CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "fixedBadMask" => (goodLambda*(2:O))

lemma fixed_mask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero (by norm_num)

def idealMask (u : O) (I : Ideal O) : ℂ := if IsCoprime I (Ideal.span {u}) then 1 else 0

def maskedSource (u : O) (β : Ideal O → ℂ) (I : Ideal O) : ℂ := β I * idealMask u I

lemma idealMask_span (u n : O) : idealMask u (Ideal.span {n}) =
    if IsCoprime n u then 1 else 0 := by
  simp only [idealMask, Ideal.isCoprime_span_singleton_iff]

lemma idealMask_primary (u : O) (I : Ideal O) (hI : Supported I) :
    idealMask u I = if IsCoprime (primaryGenerator I) u then 1 else 0 := by
  conv_lhs => rw [←primary_span_supported I hI, idealMask_span]

lemma row_mask_factor (η : Character) (u z n : O) :
    rowTwist (elementHom η) (fixedBadMask*u) 1 z n =
      (if IsCoprime n u then (1:ℂ) else 0)*
        rowTwist (elementHom η) fixedBadMask 1 z n := by
  have h := row_mask_mul η fixedBadMask u 1 z n
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda)
  simp only [one_mul] at h
  rw [h]
  split_ifs <;> simp

lemma rowWeight_mask_factor (η : Character) (u : O) (I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    rowWeight η (fixedBadMask*u) 1 1 t I =
      idealMask u I * rowWeight η fixedBadMask 1 1 t I := by
  rw [rowWeight_one_primary η (fixedBadMask*u) t I hI,
    rowWeight_one_primary η fixedBadMask t I hI, idealMask_primary u I hI]
  change elementCoeff η (primaryGenerator I) *
      (if IsCoprime (fixedBadMask*u) (primaryGenerator I) then (1:ℂ) else 0) *
      (Ideal.absNorm I:ℂ)^(Complex.I*t) =
    (if IsCoprime (primaryGenerator I) u then (1:ℂ) else 0) *
      (elementCoeff η (primaryGenerator I) *
        (if IsCoprime fixedBadMask (primaryGenerator I) then (1:ℂ) else 0) *
        (Ideal.absNorm I:ℂ)^(Complex.I*t))
  rw [IsCoprime.mul_left_iff]
  by_cases hm : IsCoprime fixedBadMask (primaryGenerator I)
  <;> by_cases hu : IsCoprime (primaryGenerator I) u
  <;> simp [hm, hu, show IsCoprime u (primaryGenerator I) ↔
      IsCoprime (primaryGenerator I) u from isCoprime_comm]

theorem exists_first_masked_character (η : Character) (e r : O)
    (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r}))
    (χ : MulChar (Residue r) ℂ) (ξ : RayCharacter) :
    ∃ τ : Character,
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r} ∧
      (∀ n : O, elementCoeff τ n =
        rowTwist (elementHom η) fixedBadMask 1 (e*r) n * maskedPrimaryHom r χ n *
          elementCoeff (CenteredMomentFixedRay.primaryRayCharacter ξ) n) ∧
      ∀ u n : O,
        rowTwist (elementHom η) (fixedBadMask*u) 1 (e*r) n * maskedPrimaryHom r χ n *
          elementCoeff (CenteredMomentFixedRay.primaryRayCharacter ξ) n =
        (if IsCoprime n u then (1:ℂ) else 0)*elementCoeff τ n := by
  obtain ⟨τ,hM,hτ,_⟩ := exists_first_character η fixedBadMask e r fixed_mask_ne_zero
    he hr (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) χ ξ
  refine ⟨τ,hM,hτ,?_⟩
  intro u n
  rw [row_mask_factor,hτ]
  ring

theorem exists_canonical_masked_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₁ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η fixedBadMask fixed_mask_ne_zero
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₁ I hI t]
    ring
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₂ I hI t]
    ring

lemma divisor_column_masked (η τ : Character) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (u : O) (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryGenerator J)
      (fun J => β J*rowWeight η (fixedBadMask*u) 1 1 t J*F (primaryGenerator J)) ξ I =
      (if L∣I then maskedSource u β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,rowWeight_mask_factor η u I hI t,hτ I hI t]
  split_ifs
  · simp only [maskedSource]; ring
  · ring

lemma sourceGaussEnergy_congr (Q : Finset (Ideal O)) (c f c' f' : Ideal O → ℂ)
    (h : ∀ I ∈ Q, Supported I → c I*f I=c' I*f' I)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : sourceGaussEnergy Q c f W K=sourceGaussEnergy Q c' f' W K := by
  unfold sourceGaussEnergy
  congr 1
  funext I
  exact h I (Finset.mem_filter.mp I.property).1 (Finset.mem_filter.mp I.property).2

lemma first_source_energy (η τ : Character) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy Q β
      (fun I => rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryGenerator I)) W K =
    sourceGaussEnergy Q (maskedSource u β) (heightCoeff τ t) W K := by
  apply sourceGaussEnergy_congr
  intro I _ hI
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  simp only [maskedSource]
  ring

lemma maskedSource_eq_of_live (u : O) (β : Ideal O → ℂ)
    (h : ∀ I, β I≠0 → IsCoprime I (Ideal.span {u})) : maskedSource u β=β := by
  funext I
  by_cases hi : β I=0
  · simp [maskedSource,hi]
  · simp [maskedSource,idealMask,h I hi]

lemma extracted_masked_coefficient (η : Character) (u : O) (C I : Ideal O)
    (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) (f : ℂ) :
    β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I)*f =
      (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t C*idealMask u I)*
        (rowWeight η fixedBadMask 1 1 t I*f) := by
  rw [map_mul,rowWeight_mask_factor η u I hI t]
  ring

lemma idealMask_generator (R I : Ideal O) :
    idealMask (idealGenerator R) I = if IsCoprime I R then 1 else 0 := by
  rw [idealMask,span_idealGenerator]

lemma maskedSource_punctured (u : O) (R : Ideal O) (β : Ideal O → ℂ) (I : Ideal O) :
    maskedSource u (fun J => if IsCoprime J R then β J else 0) I =
      if IsCoprime I R ∧ IsCoprime I (Ideal.span {u}) then β I else 0 := by
  unfold maskedSource idealMask
  split_ifs <;> simp_all

lemma first_gauss_row (η τ : Character) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => β I*
        (rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryGenerator I))) z =
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => maskedSource u β I*heightCoeff τ t I) z := by
  apply congrArg (fun c => gaussPolynomial Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c z)
  funext I
  have hI := (Finset.mem_filter.mp I.property).2
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  dsimp only [maskedSource]
  ring

theorem exists_canonical_source_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      ∀ (Q₁ Q₂ : Finset (Ideal O)) (β₁ β₂ : Ideal O → ℂ) (u₁ u₂ : O)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
      sourceGaussEnergy Q₁ β₁ (fun I => rowWeight η (fixedBadMask*u₁) 1 1 t I*
        (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) W K =
        sourceGaussEnergy Q₁ (maskedSource u₁ β₁) (heightCoeff τ₁ t) W K ∧
      sourceGaussEnergy Q₂ β₂ (fun I => rowWeight η (fixedBadMask*u₂) 1 1 t I*
        (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) W K =
        sourceGaussEnergy Q₂ (maskedSource u₂ β₂) (heightCoeff τ₂ t) W K := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩ := exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_⟩
  intro Q₁ Q₂ β₁ β₂ u₁ u₂ t W K
  constructor
  · apply sourceGaussEnergy_congr
    intro I _ hI
    rw [rowWeight_mask_factor η u₁ I hI t,h₁ I hI t]
    dsimp only [maskedSource]
    ring
  · apply sourceGaussEnergy_congr
    intro I _ hI
    rw [rowWeight_mask_factor η u₂ I hI t,h₂ I hI t]
    dsimp only [maskedSource]
    ring

def rayHeight (p : O) (k : ℕ) (τ : RayCharacter → Character) (t : ℝ) (I : Ideal O) : ℂ :=
  ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I

def extractedSource (η : Character) (u : O) (C : Ideal O)
    (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t C*idealMask u I

theorem exists_masked_radical_family (η : Character) (p : O)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) fixedBadMask p k) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η fixedBadMask 1 1 t I*residualCharacter p k (primaryGenerator I)=
          rayHeight p k τ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*residualCharacter p k (primaryGenerator I)=
          idealMask u I*rayHeight p k τ t I) ∧
      ∀ (Q : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))
          (fun I => residualCharacter p k (primaryGenerator I)) W K =
        sourceGaussEnergy Q (extractedSource η u C β t) (rayHeight p k τ t) W K := by
  obtain ⟨τ,hN,hτ⟩ := exists_radical_family η fixedBadMask p fixed_mask_ne_zero hs hpp
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) k
  refine ⟨τ,hN,hτ,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,mul_assoc,hτ I hI t]
    rfl
  · intro Q u C β t W K
    apply sourceGaussEnergy_congr
    intro I _ hI
    rw [extracted_masked_coefficient η u C I hI β t,hτ I hI t]
    rfl

theorem exists_masked_error_source (η : Character) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) fixedBadMask p (errorMovingExponent n)) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η fixedBadMask 1 1 t I*
          residualCharacter p (errorMovingExponent n) (primaryGenerator I)=
            rayHeight p (errorMovingExponent n) τ t I) ∧
      ∀ (S : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))
          (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K =
        sourceGaussEnergy (residualColumns S p hp (n+1))
          (extractedSource η u C β t) (rayHeight p (errorMovingExponent n) τ t) W K := by
  obtain ⟨τ,hN,hτ,_,henergy⟩ := exists_masked_radical_family η p hs hpp (errorMovingExponent n)
  refine ⟨τ,hN,hτ,?_⟩
  intro S u C β t W K
  rw [←henergy (residualColumns S p hp (n+1)) u C β t W K]
  apply sourceGaussEnergy_congr
  intro I hI _
  rw [residual_column_active S p hp hs n hn I hI]

lemma idealMask_mul (u : O) (C I : Ideal O) :
    idealMask u (C*I)=idealMask u C*idealMask u I := by
  simp only [idealMask,IsCoprime.mul_left_iff]
  split_ifs <;> simp_all

lemma extractedSource_whole_mask (η : Character) (u : O) (C : Ideal O)
    (hC : Supported C) (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) :
    extractedSource η u C β t I =
      maskedSource u β (C*I)*rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource,rowWeight_mask_factor η u C hC t,maskedSource,idealMask_mul]
  ring

lemma extracted_gauss_row (η : Character) (p : O) (k : ℕ) (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      rowWeight η fixedBadMask 1 1 t I*residualCharacter p k (primaryGenerator I)=
        rayHeight p k τ t I)
    (Q : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ) (t : ℝ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q =>
        (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))*
          residualCharacter p k (primaryGenerator I)) z =
    ∑ χ : RayCharacter, phaseCoeff (amplificationPhase p k) χ *
      gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q => extractedSource η u C β t I*heightCoeff (τ χ) t I) z := by
  rw [←gaussPolynomial_allocation]
  apply congrArg (fun c => gaussPolynomial Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c z)
  funext I
  have hI := (Finset.mem_filter.mp I.property).2
  rw [extracted_masked_coefficient η u C I hI β t,hτ I hI t]
  simp only [rayHeight,Finset.mul_sum,extractedSource]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem exists_masked_error_rows (η : Character) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) fixedBadMask p (errorMovingExponent n)) ∧
      ∀ (S : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ) (t : ℝ) (z : O),
      let Q := residualColumns S p hp (n+1)
      gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q =>
          (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))*
            residualCharacter p (n+1) (primaryGenerator I)) z =
      ∑ χ : RayCharacter, phaseCoeff (amplificationPhase p (errorMovingExponent n)) χ *
        gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I : supportedColumns Q => extractedSource η u C β t I*heightCoeff (τ χ) t I) z := by
  obtain ⟨τ,hN,hτ,_,_⟩ := exists_masked_radical_family η p hs hpp (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S u C β t z
  dsimp only
  rw [←extracted_gauss_row η p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) u C β t z]
  apply congrArg (fun c => gaussPolynomial Finset.univ
    (sourceGenerator (residualColumns S p hp (n+1)))
    (sourceGenerator_supported (residualColumns S p hp (n+1))) c z)
  funext I
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

lemma paired_gauss_rows (η τ₁ τ₂ : Character) (F₁ F₂ : O → ℂ)
    (h₁ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*F₁ (primaryGenerator I))
    (h₂ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*F₂ (primaryGenerator I))
    (Q₁ Q₂ : Finset (Ideal O)) (β₁ β₂ : Ideal O → ℂ) (u₁ u₂ : O) (t : ℝ) (z₁ z₂ : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q₁) (sourceGenerator_supported Q₁)
      (fun I : supportedColumns Q₁ => β₁ I*
        (rowWeight η (fixedBadMask*u₁) 1 1 t I*F₁ (primaryGenerator I))) z₁ *
    star (gaussPolynomial Finset.univ (sourceGenerator Q₂) (sourceGenerator_supported Q₂)
      (fun I : supportedColumns Q₂ => β₂ I*
        (rowWeight η (fixedBadMask*u₂) 1 1 t I*F₂ (primaryGenerator I))) z₂) =
    gaussPolynomial Finset.univ (sourceGenerator Q₁) (sourceGenerator_supported Q₁)
      (fun I : supportedColumns Q₁ => maskedSource u₁ β₁ I*heightCoeff τ₁ t I) z₁ *
    star (gaussPolynomial Finset.univ (sourceGenerator Q₂) (sourceGenerator_supported Q₂)
      (fun I : supportedColumns Q₂ => maskedSource u₂ β₂ I*heightCoeff τ₂ t I) z₂) := by
  rw [first_gauss_row η τ₁ F₁ h₁ Q₁ β₁ u₁ t z₁,
    first_gauss_row η τ₂ F₂ h₂ Q₂ β₂ u₂ t z₂]

end SevenEighths.CenteredMomentFirstMaskedFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstMaskedInput -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstMaskedFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRemainingBox
open CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma profile_combined_mask (R T seed : Ideal O) (ν : ι→Ideal O→ℂ)
    (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v *
      idealMask (idealGenerator T) (finiteTupleProduct v) =
    profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v := by
  rw [idealMask_generator]
  simp only [profileCoefficient, IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

lemma column_combined_mask (S : Finset (Tuple ι)) (R T seed : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    maskedSource (idealGenerator T)
      (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed)) =
    finiteColumnCoefficient S (profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed) := by
  funext I
  unfold maskedSource finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [←(Finset.mem_filter.mp hv).2]
  exact profile_combined_mask R T seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v

lemma input_combined_mask (s : Input ι) (R T seed : Ideal O) :
    maskedSource (idealGenerator T) (original s R seed).beta =
      (original s (R*T) seed).beta := by
  simpa only [OriginalData.beta, OriginalData.profile, original] using
    column_combined_mask (Fintype.piFinset s.pools) R T seed s.ν s.W s.P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1

lemma extracted_input (s : Input ι) (η : Character) (R T seed C : Ideal O)
    (hC : Supported C) (t : ℝ) (I : Ideal O) :
    extractedSource η (idealGenerator T) C (original s R seed).beta t I =
      (original s (R*T) seed).beta (C*I) * rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource_whole_mask η (idealGenerator T) C hC, input_combined_mask]
  rfl

theorem extracted_input_allocations (s : Input ι) (η τ : Character)
    (R T seed C I : Ideal O) (hC : Supported C) (hI : I≠0)
    (hseed : IsCoprime seed C) (t : ℝ) :
    (if IsCoprime C I then
      extractedSource η (idealGenerator T) C (original s R seed).beta t I else 0) =
    rowWeight η fixedBadMask 1 1 t C *
      ∑ B : actualAllocations s.pools C,
        frozenCoefficient B C (R*T) s.ν s.W s.P *
          (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta I := by
  have hh := original_masked_live_column s.pools s.pools_ne
    (fun i J hJ => s.prime i J hJ) C (R*T) seed I hC.1 hI hseed
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
  rw [extracted_input s η R T seed C hC t I]
  calc
    _ = rowWeight η fixedBadMask 1 1 t C *
        (if IsCoprime C I then (original s (R*T) seed).beta (C*I) else 0) := by
      split_ifs <;> ring
    _ = rowWeight η fixedBadMask 1 1 t C *
        ∑ B : actualAllocations s.pools C, frozenCoefficient B C (R*T) s.ν s.W s.P *
          finiteColumnCoefficient
            (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
            (maskedLiveProfile B C (R*T) seed s.ν s.W s.P s.W₁ s.W₂
              s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I := by
      exact congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z) hh
    _ = _ := by
      apply congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z)
      apply Finset.sum_congr rfl
      intro B _
      exact congrArg (fun z : ℂ => frozenCoefficient B C (R*T) s.ν s.W s.P * z)
        (congrFun (child_columns s C (R*T) seed B τ t).2 I)

lemma normalized_input_mask (s : Input ι) (R T seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original s R seed).columns
      (maskedSource (idealGenerator T) (original s R seed).beta)
      (heightCoeff s.η s.t) W K).re / volume s =
      normalizedGaussSource s (R*T) seed W K := by
  rw [input_combined_mask]
  rfl

lemma child_input_combined_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    maskedSource (idealGenerator T)
      (original (child s C R B τ t) (R*C) seed).beta =
      (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta := by
  rw [input_combined_mask]
  simp only [OriginalData.beta, OriginalData.profile, original, child, commonData, Input.pools,
    mul_assoc, mul_comm C T]

lemma normalized_child_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) seed).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) =
      childNormalizedGaussSource s C (R*T) seed B τ t W K := by
  have hcolumns :
      (original (child s C R B τ t) (R*C) seed).columns =
        (original (child s C (R*T) B τ t) ((R*T)*C) seed).columns :=
    (child_columns s C R seed B τ t).1.symm.trans (child_columns s C (R*T) seed B τ t).1
  have hvolume : volume (child s C R B τ t) = volume (child s C (R*T) B τ t) := by
    simp only [volume, child, commonData]
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_input_combined_mask, hcolumns, hvolume, child_character, child_height]

end SevenEighths.CenteredMomentFirstMaskedInput

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicRows -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicRows
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm
local notation "O" => HeckeFamily.O

def activeRows (rows : Finset O) (n : Fin 4→ℤ) : Finset O :=
  rows.filter (fun h => h∈dyadRows (n 1))

lemma mem_activeRows (rows : Finset O) (n : Fin 4→ℤ) (h : O) :
    h∈activeRows rows n ↔ h∈rows ∧ dyadicWeight (n 1) (normValue h)≠0 := by
  simp only [activeRows,Finset.mem_filter,mem_dyadRows]

lemma activeRows_subset (rows : Finset O) (n : Fin 4→ℤ) : activeRows rows n⊆rows :=
  Finset.filter_subset _ _

lemma activeRows_nonzero (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) : h≠0 :=
  dyadRows_ne_zero (n 1) h (Finset.mem_filter.mp hh).2

lemma activeRows_norm (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤normValue h ∧ dyadicScale (n 1)/4<normValue h ∧ normValue h<dyadicScale (n 1) :=
  ⟨normValue_ge_one h (activeRows_nonzero rows n h hh),
    dyadicWeight_support (n 1) ((mem_activeRows rows n h).mp hh).2⟩

lemma activeRows_scale_gt_one (rows : Finset O) (n : Fin 4→ℤ)
    (hne : (activeRows rows n).Nonempty) : 1<dyadicScale (n 1) := by
  obtain ⟨h,hh⟩:=hne
  exact (activeRows_norm rows n h hh).1.trans_lt (activeRows_norm rows n h hh).2.2

lemma activeRows_ball_majorant (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤(ballProfile (‖eisEmbedding h‖^2/dyadicScale (n 1))).re :=
  ballProfile_majorizes _ (dyadicScale_pos (n 1)) h (activeRows_norm rows n h hh).2.2.le

lemma row_log_window (n : ℤ) (h : O) :
    logAnnulus (Real.log (‖eisEmbedding h‖^2/dyadicScale n)) =
      (dyadicWeight n (normValue h):ℂ) := by
  by_cases hh : h=0
  · subst h
    simp only [map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div,Real.log_zero,
      logAnnulus,Real.exp_zero]
    rw [annulus_zero_high 1 le_rfl]
    rw [show normValue (0:O)=0 by simp [normValue_eq_embedding],
      dyadicWeight_zero_nonpos n 0 le_rfl,Complex.ofReal_zero]
  · rw [←normValue_eq_embedding]
    exact (actual_dyadic_log_window n (normValue h)
      (zero_lt_one.trans_le (normValue_ge_one h hh))).symm

theorem block_activeRows (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) =
    block η m A t S c C D hC hD E (activeRows rows n) W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold block activeRows
  dsimp only
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hd : h∈dyadRows (n 1)
  · simp only [hd,ite_true]
  · have hw : dyadicWeight (n 1) (normValue h)=0 := by
      simpa only [mem_dyadRows,not_not] using hd
    simp only [hd,windows,row_log_window,hw,Complex.ofReal_zero,
      mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

end SevenEighths.CenteredMomentFirstPhysicalDyadicRows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedRadiusLower -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedRadiusLower
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicRows
local notation "O" => ActualEisensteinCubic.O

lemma base_radius_identity (Z K0 Csec xi : ℝ) (hZ : 1<Z) (hC : 0<Csec) :
    Z^(K0+frequencyLoss Z (32*Csec) xi)=128*Csec*Z^K0*Z^(xi/2) := by
  have h := source_enclosure_power Z (32*Csec) K0 xi 1 hZ (by positivity) zero_lt_one
  simpa only [Real.logb_one,sub_zero,div_one] using h.symm.trans (by ring)

lemma retained_base_le (Z K0 Csec Tsec xi H0 : ℝ) (hZ : 1<Z) (hC : 0<Csec)
    (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi) :
    H0≤Z^(K0+frequencyLoss Z (32*Csec) xi) := by
  rw [base_radius_identity Z K0 Csec xi hZ hC]
  have hp : 0≤Z^(xi/2) := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hq : 0≤Z^K0 := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  calc
    H0≤4*(Tsec*Z^(xi/2)) := hrow
    _≤4*((Csec*Z^K0)*Z^(xi/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsec hp) (by norm_num)
    _≤128*Csec*Z^K0*Z^(xi/2) := by nlinarith [mul_nonneg (mul_nonneg hC.le hq) hp]

theorem common_radii_lower (Z d K0 c sigma reserve Csec Tsec xi H0 : ℝ)
    (hZ : 1<Z) (hC : 0<Csec) (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
    (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi)
    (p : O) (k : ℕ) :
    H0≤ mainCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve ∧
    H0≤errorCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve p k := by
  have hb := retained_base_le Z K0 Csec Tsec xi H0 hZ hC hsec hrow
  constructor
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c) (0:ℝ)]
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)]

theorem actual_retained_radii_lower (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec)
    (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (p : O) (k : ℕ) :
    dyadicScale n≤ mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve ∧
    dyadicScale n≤errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k := by
  apply common_radii_lower Z d _ c sigma reserve Csec Tsec xi _ hZ hC hsigma hreserve
  · simpa only [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)] using hsec
  · exact retained_scale_le _ n hn

theorem active_row_reciprocals (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec)
    (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (rows : Finset O) (n : Fin 4→ℤ)
    (hn : Retained (frequencyRadius Tsec Z xi) (n 1))
    (hne : (activeRows rows n).Nonempty) (p : O) (k : ℕ) :
    (mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve)⁻¹≤1 ∧
    (errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k)⁻¹≤1 := by
  have hb := actual_retained_radii_lower I J E hE K X Z Csec Tsec xi d c sigma reserve
    hK hX hZ hC hsigma hreserve hsec (n 1) hn p k
  have ho := (activeRows_scale_gt_one rows n hne).le
  exact ⟨inv_le_one_of_one_le₀ (ho.trans hb.1),inv_le_one_of_one_le₀ (ho.trans hb.2)⟩

end SevenEighths.CenteredMomentFirstAmplifiedRadiusLower

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentSourceAllocationEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentCommonPuncture CenteredMomentOriginalChildEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedData (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    OriginalData (liveIndices B.val) where
  S:=remainingSets B.val (fun i=>residualPool (B.val i)
    ((allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 i) (D.S i))
  R:=D.R*C
  s:=L
  nu:=fun i=>D.nu i.val
  slot:=fun i=>D.slot i.val
  lengths:=fun i=>D.lengths i.val
  W₁:=D.W₁
  W₂:=D.W₂
  X₁:=D.X₁
  X₂:=D.X₂
  Y₁:=D.Y₁
  Y₂:=D.Y₂
  B₁:=D.B₁*B.val (Sum.inr 0)
  B₂:=D.B₂*B.val (Sum.inr 1)

lemma allocated_pools (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    Fintype.piFinset (allocatedData D C L B).S=
      liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1:=rfl

lemma allocated_profile (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    (allocatedData D C L B).profile=maskedLiveProfile B.val C D.R L D.nu D.slot D.lengths
      D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂:=rfl

def commonGauss (D:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then D.beta (C*I) else 0)*heightCoeff τ t I) z

theorem common_gauss_allocation (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    commonGauss D C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (fun I=>((allocatedData D C L B).beta I)*heightCoeff τ t I) z:=by
  let Q:=residualPool C hC.1 D.columns
  let b:=fun B:actualAllocations D.S C=>frozenCoefficient B.val C D.R D.nu D.slot D.lengths
  let d:=fun (B:actualAllocations D.S C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B.val C D.R D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂) I*
        ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff τ t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I=
        ∑B,b B*d B I:=by
    have hc:=original_source_punctured_column D.S hS hp C D.R D.s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hseed D.nu D.slot D.lengths D.W₁ D.W₂
      D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    change (if IsCoprime C (I:Ideal O) then D.beta (C*I) else 0)=_ at hc
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      change (if IsCoprime C (I:Ideal O) then _ else 0)*heightCoeff τ t I=_
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  unfold commonGauss
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ _ z=_
  rw [funext he,gaussPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=>b B*w)
  have hh:=live_gaussPolynomial D.S hS hp B.val
    (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 C D.R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    (fun I=>(if L∣I then 1 else 0)*heightCoeff τ t I) z
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ (d B) z=_ at hh
  rw [hh]
  congr 1
  funext I
  change _=finiteColumnCoefficient _ (allocatedData D C L B).profile I*heightCoeff τ t I
  rw [allocated_profile,maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  rw [allocated_pools]
  ring

theorem normalized_common_gauss_allocation (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonGauss D C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [common_gauss_allocation D hS hp C hC hseed τ t L z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  simp only [OriginalData.coefficient,gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [heightCoeff_eq_fixed_rowWeight τ t I (Finset.mem_filter.mp I.property).2]
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAllocationGaussEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAllocationGaussEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentAddedZeroUniform
open CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def commonEnergy (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, ‖commonGauss D C hC τ t L z‖^2 *
    (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re

def allocatedEnergy (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (allocatedData D C L B).columns
    (allocatedData D C L B).beta (heightCoeff τ t) W K).re

lemma common_summable (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖commonGauss D C hC τ t L z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).summable

lemma allocated_hasSum (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O =>
      ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
        (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (allocatedEnergy D C L B τ t W K) :=
  gaussEnergy_hasSum_re _ _ _ _ W K hK

lemma allocated_nonneg (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤allocatedEnergy D C L B τ t W K := by
  rw [← (allocated_hasSum D C L B τ t W K hK).tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

theorem common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I∈D.S i, I≠0) (hp : ∀ i, ∀ I∈D.S (Sum.inl i), Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    commonEnergy D C hC τ t L W K ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K := by
  unfold commonEnergy
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows, ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
          (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [common_gauss_allocation D hS hp C hC hseed τ t L z]
      have hc := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B : actualAllocations D.S C =>
            frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
              gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
                (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z))
        (hW z)
      simpa only [Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using hc
    _ = ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          ∑ z∈rows, ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
            (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z))
        (allocated_hasSum D C L B τ t W K hK)

def rawVolume (D : OriginalData ι) : ℝ :=
  (D.X₁*D.X₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂)) * ∏ i,D.lengths i

lemma rawVolume_pos (D : OriginalData ι) (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂)
    (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) (hP : ∀ i,0<D.lengths i) : 0< rawVolume D := by
  apply mul_pos (div_pos (mul_pos hX₁ hX₂) _)
    (Finset.prod_pos (fun i _ => hP i))
  exact mul_pos (CenteredMomentFirstScale.norm_pos _ hB₁) (CenteredMomentFirstScale.norm_pos _ hB₂)

lemma allocated_rawVolume_mul (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) :
    rawVolume (allocatedData D C L B) * rawReduction B.val D.lengths = rawVolume D := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hv := remainingRaw_source B.val hB D.B₁ D.B₂ hB₁ hB₂ (D.X₁*D.X₂) D.lengths
  change _ = rawVolume (allocatedData D C L B) at hv
  rw [← hv]
  exact raw_scale_identity B.val hB _ D.lengths

lemma allocated_rawVolume (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    rawVolume (allocatedData D C L B) = rawVolume D / rawReduction B.val D.lengths := by
  have hr := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  exact (eq_div_iff hr.ne').mpr (allocated_rawVolume_mul D C L B hB₁ hB₂)

lemma rawVolume_both (D : OriginalData ι) (T : ℝ)
    (hX : D.X₁*D.X₂=T) (hY : D.Y₁*D.Y₂=T) :
    rawVolume D=(T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i ∧
    rawVolume D=(D.Y₁*D.Y₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i := by
  simp only [rawVolume,hX,hY,and_self]

def frozenControl (B : Tuple ι) (M : ι → ℝ) : ℝ :=
  ∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),M i

lemma frozenControl_nonneg (B : Tuple ι) (M : ι → ℝ)
    (hM : ∀ i,0≤M i) : 0≤frozenControl B M :=
  Finset.prod_nonneg (fun i _ => hM i)

lemma frozen_norm_bound (D : OriginalData ι) (C : Ideal O)
    (B : actualAllocations D.S C) (M : ι → ℝ) (_hM : ∀ i,0≤M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hW : ∀ i x,‖D.slot i x‖≤M i) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖≤frozenControl B.val M := by
  unfold frozenCoefficient frozenControl
  rw [norm_mul]
  have hc : ‖(if IsCoprime C D.R then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  apply (mul_le_of_le_one_right (norm_nonneg _) hc).trans
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i hi
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hν i _)).trans (hW i _)

theorem frozen_normalized_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤N)
    (C : Ideal O) (hC : C≠0) (B : actualAllocations D.S C)
    (M : ι → ℝ) (hM : ∀ i,0≤M i) (hP : ∀ i,0<D.lengths i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤M i)
    (hW : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths ≤
      (max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2 := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hR := rawReduction_pos B.val hB D.lengths hP
  have hN := CenteredMomentFirstScale.norm_pos C hC
  by_cases hz : frozenCoefficient B.val C D.R D.nu D.slot D.lengths=0
  · rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    positivity
  · have hm := frozen_norm_bound D C B M hM hν hWnorm
    have hh := (actual_reduction_norm B.val hB C D.R
      (Finset.mem_filter.mp B.property).2 D.nu D.slot D.lengths hP a b ha hW hz).2
    have he : (max 1 b)^Fintype.card ι≤(max 1 b)^N :=
      pow_le_pow_right₀ (le_max_left _ _) hcard
    have hi : (1:ℝ)/rawReduction B.val D.lengths ≤ (max 1 b)^N/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh.trans (mul_le_mul_of_nonneg_right he hR.le)
    calc
      _ ≤ (frozenControl B.val M)^2/rawReduction B.val D.lengths :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (frozenControl B.val M)^2*(1/rawReduction B.val D.lengths) := by ring
      _ ≤ (frozenControl B.val M)^2*((max 1 b)^N/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

theorem normalized_common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        (‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  have hV := rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP
  have he := div_le_div_of_nonneg_right
    (common_energy_allocation D hS hp C hC hseed τ t L W K hK hW) hV.le
  apply he.trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations D.S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hR := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
  field_simp

theorem normalized_common_energy_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤N)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) (M : ι → ℝ) (hM : ∀ i,0≤M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤M i)
    (hslot : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      (max 1 b)^N * ((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑ B : actualAllocations D.S C, (frozenControl B.val M)^2 *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  apply (normalized_common_energy_allocation D hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP).trans
  calc
    _ ≤ ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ((max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      have hVa : 0< rawVolume (allocatedData D C L B) := by
        rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
        exact div_pos (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)
          (rawReduction_pos B.val (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP)
      exact mul_le_mul_of_nonneg_right
        (frozen_normalized_bound N a b ha D hcard C hC.1 B M hM hP hν hWnorm hslot)
        (div_nonneg (allocated_nonneg D C L B τ t W K hK hW) hVa.le)
    _ = _ := by
      simp only [mul_assoc,← Finset.mul_sum]
      ring

theorem normalized_common_as_tsum (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hV : 0< rawVolume D) :
    (∑' z : O, ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) =
      commonEnergy D C hC τ t L W K/rawVolume D := by
  have hn (z : O) : ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 =
      ‖commonGauss D C hC τ t L z‖^2/rawVolume D := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow,inv_pow,Real.sq_sqrt hV.le]
    ring
  simp_rw [hn,div_mul_eq_mul_div]
  exact tsum_div_const

theorem allocated_sum_hasSum (D : OriginalData ι) (C L : Ideal O)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ∑ B : actualAllocations D.S C,
      ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
        (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
        (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re))
      (∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K) := by
  exact hasSum_sum (fun B _ => (allocated_hasSum D C L B τ t W K hK).mul_left _)

theorem original_radial_bound (N : ℕ) (a b : ℝ) (ha : 0<a) :
    ∃ F : ℝ,0<F ∧ ∀ {κ : Type*} [Fintype κ],∀ D : OriginalData κ,
      Fintype.card κ≤N →
      (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
      ∀ (C : Ideal O) (hC : Supported C), D.s∣C →
      ∀ (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T : ℝ),
      0<K → (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      0<D.X₁ → 0<D.X₂ → D.B₁≠0 → D.B₂≠0 →
      (∀ i,0<D.lengths i) → D.X₁*D.X₂=T → D.Y₁*D.Y₂=T →
      ∀ M : κ → ℝ,(∀ i,0≤M i) → (∀ i I,‖D.nu i I‖≤1) →
      (∀ i x,‖D.slot i x‖≤M i) →
      (∀ i,Function.support (D.slot i)⊆Set.Icc a b) →
      (∑' z : O,
        ‖(Real.sqrt ((T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i):ℂ)⁻¹ *
          commonGauss D C hC τ t L z‖^2 * (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) ≤
        F*((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          ∑ B : actualAllocations D.S C,(frozenControl B.val M)^2 *
            (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  refine ⟨(max 1 b)^N,pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _,?_⟩
  intro κ _ D hcard hS hp C hC hseed τ t L W K T hK hW hX₁ hX₂ hB₁ hB₂ hP hX hY M hM hν hWnorm hslot
  rw [← (rawVolume_both D T hX hY).1,
    normalized_common_as_tsum D C hC τ t L W K (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)]
  exact normalized_common_energy_bound N a b ha D hcard hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP M hM hν hWnorm hslot

end SevenEighths.CenteredMomentFirstAllocationGaussEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocationControl -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocationControlDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma frozen_live_control (B : Tuple ι) (M : ι→ℝ) :
    frozenControl B M * (∏i : liveIndices B,M i.val) = ∏i,M i := by
  rw [Finset.prod_coe_sort (liveIndices B) M]
  unfold frozenControl liveIndices
  rw [mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i=>B (Sum.inl i)=1) M

lemma frozen_child_control (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t : ℝ) :
    (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2 = (∏i,s.M i)^2 := by
  rw [←mul_pow]
  exact congrArg (fun x:ℝ=>x^2) (frozen_live_control B.val s.M)

lemma allocated_control_sum (s : Input ι) (C R : Ideal O)
    (τ : HeckeFamily.Character) (t : ℝ) :
    (∑B : actualAllocations s.pools C,
      (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) =
      ((actualAllocations s.pools C).card:ℝ) * (∏i,s.M i)^2 := by
  simp only [frozen_child_control,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    nsmul_eq_mul]

theorem allocated_control_mass (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{κ : Type*}[Fintype κ],Fintype.card κ≤N →
      ∀(s : Input κ)(C R : Ideal O),C≠0 →
      ∀(τ : HeckeFamily.Character)(t : ℝ),
        ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          (∑B : actualAllocations s.pools C,
            (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) ≤
          D*(Ideal.absNorm C:ℝ)^(ε-1)*(∏i,s.M i)^2 := by
  obtain ⟨D,hD,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro κ _ hn s C R hC τ t
  have hN : (0:ℝ)<Ideal.absNorm C := CenteredMomentFirstScale.norm_pos C hC
  have hh := hcard (ι:=κ⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin];omega)
    s.pools C hC
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hh 2
  rw [mul_pow,←Real.rpow_mul_natCast hN.le,show ε/2*(2:ℕ)=ε by norm_num] at hs
  rw [allocated_control_sum]
  calc
    _ = (((actualAllocations s.pools C).card:ℝ)^2/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 := by ring
    _ ≤ (D^2*(Ideal.absNorm C:ℝ)^ε/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs hN.le) (sq_nonneg _)
    _ = _ := by rw [Real.rpow_sub hN,Real.rpow_one];ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI

end

