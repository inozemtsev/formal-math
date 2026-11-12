module

public import Green64.Library.OAI.NumberTheory.DirichletL.Dictionary.InverseRawRadial
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part014
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part011
public import Green64.Library.OAI.NumberTheory.DirichletL.Dictionary.InverseRawFourier
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part023
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Dictionary / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Dictionary.InverseRawRealRadial -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRealRadial
open InverseInitialConjugateEnergy ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

theorem exists_real_raw_radial_majorant:
    ∃Φ:𝓢(ℝ,ℂ),HasCompactSupport (Φ:ℝ→ℂ) ∧
      (∀x,0≤(Φ x).re) ∧ (∀x,(Φ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) 1,Φ x=1):=by
  have hsub:Set.Icc (0:ℝ) 1⊆Set.Ioo (-1) 2:=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) 2:=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  have hvc:=HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem smoothedEnergy_eq_complex_norm (Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hreal:∀x,(Φ x).im=0)
    (H:ℝ)(hH:0<H)(f:O→ℂ):
    smoothedEnergy Φ H f=
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/H)*(‖f u‖^2:ℝ)‖:=by
  rw [real_smoothed_sum_eq Φ (fun x _=>hreal x) hH,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothedEnergy_nonneg Φ (fun x _=>hΦ x) hH f)]

end SevenEighths.DetectorDictionaryInverseRawRealRadial

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialMarkedDictionary -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialMarkedDictionary
open HeckeFamily HeckeDyadic InverseInitialRawDictionary InverseInitialConjugateEnergy
open InverseInitialPoissonBridge UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem indexed_mark_initial {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*idealCoeff χ (P i))=
      ∑i∈T,A i*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hc]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A i*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η (P i)*CanonicalRowCompletion.idealRowHom u (P i))*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem indexed_conjugate_mark_norm {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S)
    (hη : ∀i∈T,A i≠0 → η (P i)≠0) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i)))‖=
      ‖∑i∈T,(star (A i)/η (P i))*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑i∈T,(star (A i)/η (P i))*idealCoeff χ (P i))=
      star (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i))) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i=0
    · simp [ha]
    · rw [hrow]
      field_simp [hη i hi ha]
  rw [←indexed_mark_initial T P (fun i=>star (A i)/η (P i)) η χ u hrow W Z r z σ freq hZ S hc,hm]
  simp only [norm_mul,norm_star]

theorem conjugate_mark_product {ι : Type*} [Fintype ι]
    (T : ι→Finset (Ideal O)) (A : ι→Ideal O→ℂ) (u : O) :
    (∏i,∑P∈T i,A i P*star (CanonicalRowCompletion.idealRowHom u P))=
      ∑p∈Fintype.piFinset T,(∏i,A i (p i))*
        star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.prod_mul_distrib,map_prod,star_prod]

end SevenEighths.InverseInitialMarkedDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalSlots -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialPhysicalSlots
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialMarkedDictionary
open InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def livePrimes (V : ℝ→ℂ) (b D : ℝ) : Finset (Ideal O) :=
  ((HeckePrimeAnnular.annulusSet b D).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)).filter
      (fun P=>V ((P.absNorm:ℝ)/D)≠0)

omit [NeZero M] in
theorem livePrime_data (V : ℝ→ℂ) (a b D : ℝ) (hD : 0<D)
    (hV : ∀x,V x≠0 → x∈Set.Icc a b) (P : Ideal O) (hp : P∈livePrimes M H V b D) :
    Prime P ∧ P∈RayQuotient.identityClass M H ∧ a*D≤(P.absNorm:ℝ) ∧ (P.absNorm:ℝ)≤b*D := by
  obtain ⟨hp,hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,hp,hr⟩ := Finset.mem_filter.mp hp
  exact ⟨hp,hr,(le_div_iff₀ hD).mp (hV _ hv).1,(div_le_iff₀ hD).mp (hV _ hv).2⟩

omit [NeZero M] in
theorem amplitude_eq_live (u : O) (V : ℝ→ℂ) (b Z ell : ℝ) (ζ : ℂ) (hZ : 0<Z) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u V b (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈livePrimes M H V b (Z^ell),
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u P) := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [normalization_eq Z ell hZ]
  congr 1
  rw [livePrimes]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs with hv
  · change star (CanonicalRowCompletion.idealRowHom u P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u P)
    ring
  · simp only [not_not] at hv
    simp [hv]

theorem slot_normalization {ι : Type*} [Fintype ι] (Z : ℝ) (hZ : 0<Z) (ell : ι→ℝ) :
    (∏i,((Z^(-ell i/2):ℝ):ℂ))=((Z^(-(∑i,ell i)/2):ℝ):ℂ) := by
  rw [←Complex.ofReal_prod,←Real.rpow_sum_of_pos hZ]
  congr 2
  simp only [neg_div,Finset.sum_div,Finset.sum_neg_distrib]

omit [NeZero M] in
theorem amplitude_product_eq_tuples {ι : Type*} [Fintype ι] (u : O)
    (V : ι→ℝ→ℂ) (b ell : ι→ℝ) (ζ : ι→ℂ) (Z : ℝ) (hZ : 0<Z) :
    (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (Z^(ell i)) (ζ i))=
      ((Z^(-(∑i,ell i)/2):ℝ):ℂ)*
        ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
        (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))*
          star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  simp_rw [amplitude_eq_live M H _ _ _ _ _ _ hZ]
  rw [Finset.prod_mul_distrib,slot_normalization Z hZ,conjugate_mark_product]

omit [NeZero M] in
theorem physical_slots_norm_initial {ι : Type*} [Fintype ι]
    (data : RowData) (u : NonzeroElement) (W : ℝ→ℂ) (V : ι→ℝ→ℂ)
    (Z r σ freq bW : ℝ) (a b ell : ι→ℝ) (ζ : ι→ℂ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤bW) (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i)) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
      (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
        fixedBase data.η data.m data.f (∏i,p i))*
      originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
        (∏i,p i) (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r (∑i,ell i) u.val‖ := by
  let T := fun i=>livePrimes M H (V i) (b i) (Z^(ell i))
  let A := fun p:ι→Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p : ι→Ideal O) (hp : p∈Fintype.piFinset T) (_ha : A p≠0) :
      fixedBase data.η data.m data.f (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hpi := Fintype.mem_piFinset.mp hp i
    have hd := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) hpi
    exact base_nonzero_prime data (p i) hd.1 ((hlarge i).trans_le hd.2.2.1)
  have he := indexed_conjugate_mark_norm (Fintype.piFinset T) (fun p=>∏i,p i) A
    (fixedBase data.η data.m data.f) (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r (∑i,ell i) σ freq hZ (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial (data.character u) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset T,A p*star (CanonicalRowCompletion.idealRowHom u (∏i,p i)))‖=_
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

omit [NeZero M] in
theorem live_tuple_injective {ι : Type*} [Fintype ι]
    (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hi := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hj := livePrime_data M H (V j) (a j) (b j) (Z^(ell j))
    (Real.rpow_pos_of_pos hZ _) (hV j) (p j) (Fintype.mem_piFinset.mp hp j)
  rw [he] at hi
  rcases hsep i j hij with h|h <;> linarith [hi.2.2.1,hi.2.2.2,hj.2.2.1,hj.2.2.2]

omit [NeZero M] in
theorem live_tuple_admissible {ι : Type*} [Fintype ι]
    (data : RowData) (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) :
    CanonicalQuadraticSieve.Admissible (∏i,p i) := by
  have hd i := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hs (i : ι) : CanonicalQuadraticSieve.Supported (p i) := by
    by_contra hn
    exact base_nonzero_prime data (p i) (hd i).1 ((hlarge i).trans_le (hd i).2.2.1)
      (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd (p i) hn)
  have hi := live_tuple_injective M H V a b ell Z hZ hV hsep p hp
  have hsprod : CanonicalQuadraticSieve.Supported (∏i,p i) := by
    have hh (S : Finset ι) : CanonicalQuadraticSieve.Supported (∏i∈S,p i) := by
      induction S using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi]
        exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs i,ih⟩
    exact hh Finset.univ
  refine ⟨hsprod.1,?_,?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime (hd i).1).isMaximal (hd i).1.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime (hd j).1).isMaximal (hd j).1.ne_zero
      exact (Ideal.isCoprime_of_isMaximal (hi.ne hij)).isRelPrime
    · intro i _
      exact (hd i).1.squarefree
  · intro P hP
    exact hsprod.2 P hP

end SevenEighths.InverseInitialPhysicalSlots

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PrimePool -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical Topology ContDiff
open Filter
namespace SevenEighths.CenteredMomentPrimePool
open HeckeFamily PNT.AnnularPrimeMass CenteredMomentAmplificationCount

def primePool (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  annularPrimeIdeals (RayQuotient.identityClass M H) a b x \ S

theorem annular_weighted_card_bound (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (a b B x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hW : ∀ y, W y ≤ B) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x ≤
      ((annularPrimeIdeals C a b x \ S).card : ℝ) * (B * a^(-5/6 : ℝ)) * x^(-5/6 : ℝ) := by
  rw [weightedPrimeSumDeleted_eq_annular C S W ha hab hsupp hx]
  calc
    _ ≤ ∑ _P ∈ annularPrimeIdeals C a b x \ S, B*(a*x)^(-5/6 : ℝ) := by
      apply Finset.sum_le_sum
      intro P hP
      have hn := (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx (Finset.mem_sdiff.mp hP).1).1
      apply mul_le_mul (hW _) _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB
      exact Real.rpow_le_rpow_of_nonpos (mul_pos ha hx) (by nlinarith) (by norm_num)
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,Real.mul_rpow ha.le hx.le]
      ring

section FixedRay
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

include hH

theorem eventually_primePool_card (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0)
    (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hbound : ∀ y, W y ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c*x/Real.log x ≤ (primePool M H S a b x).card := by
  obtain ⟨c,hcpos,hlower⟩ := RayPrimeNormalizer.eventually_lower_bound M H hH S W hW hc hp hW0 hWne
  let D : ℝ := B*a^(-5/6 : ℝ)
  have hD : 0 < D := mul_pos hB (Real.rpow_pos_of_pos ha _)
  refine ⟨c/D,div_pos hcpos hD,?_⟩
  filter_upwards [hlower,eventually_gt_atTop (1 : ℝ)] with x hlow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hu := annular_weighted_card_bound (RayQuotient.identityClass M H) S W a b B x
    ha hab hB.le hsupp hbound hx0
  change weightedPrimeSumDeleted _ S W x ≤ (primePool M H S a b x).card * D * x^(-5/6 : ℝ) at hu
  change c*x^(1/6 : ℝ)/Real.log x ≤ weightedPrimeSumDeleted _ S W x at hlow
  have hpower : x*x^(-5/6 : ℝ) = x^(1/6 : ℝ) := by
    calc
      _ = x^(1 : ℝ)*x^(-5/6 : ℝ) := by rw [Real.rpow_one]
      _ = x^((1 : ℝ)+(-5/6)) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hmul : (c*x/Real.log x)*x^(-5/6 : ℝ) ≤
      ((primePool M H S a b x).card * D)*x^(-5/6 : ℝ) := by
    calc
      _ = c*(x*x^(-5/6 : ℝ))/Real.log x := by ring
      _ = _ := by rw [hpower]
      _ ≤ _ := hlow.trans hu
  have hcancel := le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hx0 (-5/6 : ℝ))
  convert (div_le_iff₀ hD).mpr hcancel using 1 ; ring

end FixedRay

def eligiblePool (P : Finset (Ideal O)) (R : Ideal O) : Finset (Ideal O) :=
  P.filter (fun Q => ¬Q ∣ R)

theorem eligiblePool_card_lower (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q)
    (R : Ideal O) (hR : R ≠ 0) (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ Q ∈ P, Z^ℓ ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) :
    (P.card : ℝ) - B/ℓ ≤ (eligiblePool P R).card := by
  have hbad := large_prime_divisor_count (P.filter (fun Q => Q ∣ R))
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1) R hR
    (fun Q hQ => (Finset.mem_filter.mp hQ).2) Z ℓ B hZ hℓ
    (fun Q hQ => hlower Q (Finset.mem_filter.mp hQ).1) hupper
  have he := Finset.card_filter_add_card_filter_not (s := P) (fun Q => Q ∣ R)
  have her : ((P.filter (fun Q => Q ∣ R)).card : ℝ) + (eligiblePool P R).card = P.card := by
    exact_mod_cast he
  linarith

theorem eligiblePool_half (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q)
    (R : Ideal O) (hR : R ≠ 0) (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ Q ∈ P, Z^ℓ ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) (hsize : 2*(B/ℓ) ≤ P.card) :
    (P.card : ℝ)/2 ≤ (eligiblePool P R).card := by
  have h := eligiblePool_card_lower P hp R hR Z ℓ B hZ hℓ hlower hupper
  linarith

end SevenEighths.CenteredMomentPrimePool

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPrimePool -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawScaleEnergy (data : RowData) (W : ℝ→ℂ) (U D V E : ℝ) : Prop :=
  ∀ R : Finset NonzeroElement,
    (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
    ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E

def typedPrimePool (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) : Finset PrimeIdeal :=
  (CenteredMomentPrimePool.primePool M H S a b x).subtype Prime

theorem typedPrimePool_card (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) :
    (typedPrimePool M H S a b x).card=
      (CenteredMomentPrimePool.primePool M H S a b x).card := by
  rw [typedPrimePool,Finset.card_subtype]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro P hP
  exact ((PNT.AnnularPrimeMass.mem_annularPrimeIdeals _ _ _ _ _).mp
    (Finset.mem_sdiff.mp hP).1).2.1

theorem typedPrimePool_norm (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (a b x : ℝ) (ha : 0≤a) (hab : a≤b) (hx : 0<x)
    (P : PrimeIdeal) (hP : P∈typedPrimePool M H S a b x) :
    (P.val.absNorm : ℝ)≤x*b := by
  have hh := Finset.mem_subtype.mp hP
  exact (PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp hh).1).2

theorem eventually_fixed_ray_amplification
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y, 0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y, φ y≤B) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (data : RowData) (rows : Finset FreeRow) (W : ℝ→ℂ)
        (wa wb D U E : ℝ),
      0<wa → 0≤wb → Function.support W⊆Icc wa wb → ContDiff ℝ ∞ W →
      0<D → (∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      RawScaleEnergy data W U D (x*b) E →
      RawScaleEnergy data (scaleProfile W) U D (x*b) E →
      (∑ u∈rows, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2)≤
        4*(1+2*Real.log (x*b))*E*Real.log x/(c*x) := by
  obtain ⟨c,hc,hcard⟩ := CenteredMomentPrimePool.eventually_primePool_card M H hH S
    φ hφ hφc hφp hφ0 hφne a b B ha hab hB hφs hφB
  have hb : 0<b := ha.trans_le hab
  refine ⟨c,hc,?_⟩
  filter_upwards [hcard,eventually_gt_atTop (1 : ℝ),eventually_ge_atTop (1/b)] with x hcard hx hxB
  intro data rows W wa wb D U E hwa hwb hWs hW hD hrows hraw0 hraw1
  have hx0 : 0<x := zero_lt_one.trans hx
  have hxblog : 1≤x*b := (div_le_iff₀ hb).mp hxB
  have hlog : 0<Real.log x := Real.log_pos hx
  have hc' : c*x/Real.log x≤((typedPrimePool M H S a b x).card : ℝ) := by
    rw [typedPrimePool_card]
    exact hcard
  have havg := averaged_energy data rows (typedPrimePool M H S a b x) W wa wb hwa hwb
    hWs hW D U (x*b) E hD hxblog hrows
    (fun P hP => typedPrimePool_norm M H S a b x ha.le hab hx0 P hP) hraw0 hraw1
  have hsum : 0≤∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := (mul_le_mul_of_nonneg_right hc' hsum).trans havg
  apply (le_div_iff₀ (mul_pos hc hx0)).mpr
  calc
    _ = (c*x/Real.log x*(∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2))*Real.log x := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hh hlog.le

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationBudget -/

section

namespace OAI

noncomputable section
open Filter
namespace SevenEighths.HeckeInverseAmplification

def amplificationPower (c r : ℝ) : ℝ := max 0 (((1+c)*r-1)/6)
def sourceExponent (r : ℝ) : ℝ := max 1 ((1+5*r)/6)

theorem amplificationPower_nonneg (c r : ℝ) : 0≤amplificationPower c r := le_max_left _ _

theorem amplificationPower_upper (c r R : ℝ) (hc : c≤1) (hr : 0≤ r)
    (hrR : r≤R) : amplificationPower c r≤R/3 := by
  apply max_le (by linarith)
  have hh := mul_le_mul_of_nonneg_right hc hr
  nlinarith

theorem amplified_exponent (c r : ℝ) :
    1+5*amplificationPower c r=max 1 ((1+5*(1+c)*r)/6) := by
  unfold amplificationPower
  by_cases h : 0≤((1+c)*r-1)/6
  · rw [max_eq_right h,max_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (by linarith)]
    ring

theorem amplified_exponent_le (c r R : ℝ) (hc : 0≤ c) (hrR : r≤R)
    (hR : 0≤R) : 1+5*amplificationPower c r≤ sourceExponent r+5*c*R/6 := by
  rw [amplified_exponent]
  apply max_le
  · have hh := le_max_left 1 ((1+5*r)/6)
    unfold sourceExponent
    nlinarith [mul_nonneg hc hR]
  · have hh := le_max_right 1 ((1+5*r)/6)
    have hh' := mul_le_mul_of_nonneg_left hrR hc
    unfold sourceExponent
    nlinarith

theorem exists_amplification_budget (R ε : ℝ) (hR : 0≤R) (hε : 0<ε) :
    ∃ c κ : ℝ, 0<c ∧ c≤1 ∧ 0<κ ∧
      ∀ r : ℝ, 0≤ r → r≤R →
      1+5*amplificationPower c r+κ*(1+6*amplificationPower c r+r)≤
        sourceExponent r+ε/2 := by
  let c := min 1 (ε/(4*(R+1)))
  let κ := ε/(4*(1+3*R))
  have hc : 0<c := lt_min zero_lt_one (div_pos hε (by positivity))
  have hκ : 0<κ := div_pos hε (by positivity)
  have hc1 : c≤1 := min_le_left _ _
  have hcb : c*(4*(R+1))≤ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hκb : κ*(4*(1+3*R))=ε := by dsimp [κ]; field_simp
  refine ⟨c,κ,hc,hc1,hκ,?_⟩
  intro r hr hrR
  have hp := amplificationPower_upper c r R hc1 hr hrR
  have he := amplified_exponent_le c r R hc.le hrR hR
  have hraw : κ*(1+6*amplificationPower c r+r)≤κ*(1+3*R) := by
    apply mul_le_mul_of_nonneg_left _ hκ.le
    linarith
  nlinarith

theorem logarithmic_cost_eventually (A b P η : ℝ) (hA : 1≤A)
    (hbA : 1≤b*A) (hP : 0≤P) (hη : 0<η) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ U : ℝ in atTop, ∀ p : ℝ, 0≤p → p≤P →
      (1+2*Real.log (b*(A*U^p)))*Real.log (A*U^p)≤K*U^η := by
  let K := (1+2*Real.log (b*A)+2*P)*(Real.log A+P)
  have hLA : 0≤Real.log A := Real.log_nonneg hA
  have hLB : 0≤Real.log (b*A) := Real.log_nonneg hbA
  have hK : 0≤K := mul_nonneg (by positivity) (by positivity)
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℝ)] with U hlog hLU hU
  intro p hp hpP
  have hUp : 0<U := zero_lt_one.trans_le hU
  have hpow : 0<U^p := Real.rpow_pos_of_pos hUp _
  have hx : 1≤A*U^p := one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hU hp)
  have hlogx : Real.log (A*U^p)=Real.log A+p*Real.log U := by
    rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hA)) hpow.ne',Real.log_rpow hUp]
  have hlogbx : Real.log (b*(A*U^p))=Real.log (b*A)+p*Real.log U := by
    rw [show b*(A*U^p)=b*A*U^p by ring,
      Real.log_mul (ne_of_gt (zero_lt_one.trans_le hbA)) hpow.ne',Real.log_rpow hUp]
  have hfirst : 1+2*Real.log (b*(A*U^p))≤(1+2*Real.log (b*A)+2*P)*Real.log U := by
    rw [hlogbx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLB]
  have hsecond : Real.log (A*U^p)≤(Real.log A+P)*Real.log U := by
    rw [hlogx]
    nlinarith [mul_le_mul_of_nonneg_right hpP (by linarith : 0≤Real.log U),
      mul_le_mul_of_nonneg_left hLU hLA]
  have hsq : (Real.log U)^2≤U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  calc
    _ ≤ ((1+2*Real.log (b*A)+2*P)*Real.log U)*((Real.log A+P)*Real.log U) :=
      mul_le_mul hfirst hsecond (Real.log_nonneg hx) (by positivity)
    _ = K*(Real.log U)^2 := by dsimp [K]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hK

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationPowers -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeInverseAmplification

theorem amplified_norm_power (U A b p : ℝ) (hU : 0<U) :
    U*(b*(A*U^p))^6=(b*A)^6*U^(1+6*p) := by
  have h6 : (U^p)^6=U^(6*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
    congr 1
    norm_num
    ring
  calc
    _ = (b*A)^6*(U^(1 : ℝ)*U^(6*p)) := by
      rw [show b*(A*U^p)=(b*A)*U^p by ring,mul_pow,h6,Real.rpow_one]
      ring
    _ = _ := by rw [←Real.rpow_add hU]

theorem amplified_energy_power (U A b p r κ : ℝ) (hU : 0<U) :
    (U*(b*(A*U^p))^6)*((U*(b*(A*U^p))^6)*U^r)^κ/(A*U^p)=
      ((b*A)^6*((b*A)^6)^κ/A)*U^(1+5*p+κ*(1+6*p+r)) := by
  rw [amplified_norm_power U A b p hU]
  have hHD : ((b*A)^6*U^(1+6*p))*U^r=(b*A)^6*U^(1+6*p+r) := by
    rw [mul_assoc,←Real.rpow_add hU]
  rw [hHD,Real.mul_rpow (by positivity) (Real.rpow_nonneg hU.le _),
    ←Real.rpow_mul hU.le]
  calc
    _ = ((b*A)^6*((b*A)^6)^κ/A)*
        ((U^(1+6*p)*U^((1+6*p+r)*κ))/U^p) := by ring
    _ = ((b*A)^6*((b*A)^6)^κ/A)*U^((1+6*p)+(1+6*p+r)*κ-p) := by
      rw [←Real.rpow_add hU,←Real.rpow_sub hU]
    _ = _ := by congr 2; ring

theorem fixed_multiplier_lower (U A p : ℝ) (hU : 1≤U) (hA : 0≤A) (hp : 0≤p) :
    A≤A*U^p := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hU hp) hA

theorem amplified_norm_dominates (U A b c r : ℝ) (hU : 1≤U) (hbA : 1≤b*A) :
    (U^r)^(1+c)≤U*(b*(A*U^(amplificationPower c r)))^6 := by
  have hUp : 0<U := zero_lt_one.trans_le hU
  rw [amplified_norm_power U A b _ hUp,←Real.rpow_mul hUp.le]
  have he : r*(1+c)≤1+6*amplificationPower c r := by
    have hh := le_max_right 0 (((1+c)*r-1)/6)
    unfold amplificationPower
    nlinarith
  have hp := Real.rpow_le_rpow_of_exponent_le hU he
  have hconst : (1 : ℝ)≤(b*A)^6 := one_le_pow₀ hbA
  exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hUp.le _) hconst)

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRaw -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def RawMoment (data : RowData) (W : ℝ→ℂ) (c κ C : ℝ) : Prop :=
  ∀ H D : ℝ, 1≤H → 0<D → D^(1+c)≤H →
    ∀ rows : Finset NonzeroElement,
      (∀ v∈rows, ((Ideal.span {v.val}).absNorm : ℝ)≤H) →
      ∑ v∈rows, ‖polynomial (data.character v) true W D 0 0‖^2≤
        C*H*(H*max 1 D)^κ

theorem RawMoment.scaleEnergy {data : RowData} {W : ℝ→ℂ} {c κ C : ℝ}
    (hraw : RawMoment data W c κ C) (hc : 0≤ c) (hκ : 0≤κ) (hC : 0≤C)
    (U D V : ℝ) (hD : 1≤D) (hH : 1≤U*V^6) (hHD : D^(1+c)≤U*V^6) :
    RawScaleEnergy data W U D V (C*(U*V^6)*((U*V^6)*D)^κ) := by
  intro rows hrows l hl
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hHp : 0<U*V^6 := zero_lt_one.trans_le hH
  have hexp : Real.exp l≤D := by
    rw [←Real.exp_log hDp]
    exact Real.exp_le_exp.mpr hl.2
  have hp : (Real.exp l)^(1+c)≤U*V^6 :=
    (Real.rpow_le_rpow (Real.exp_pos l).le hexp (by linarith)).trans hHD
  have hh := hraw (U*V^6) (Real.exp l) hH (Real.exp_pos l) hp rows hrows
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hHp.le)
  apply Real.rpow_le_rpow (by positivity) _ hκ
  exact mul_le_mul_of_nonneg_left (max_le hD hexp) hHp.le

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Dictionary.InverseRawEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory
namespace SevenEighths.DetectorDictionaryInverseRawFourier
open HeckeFamily HeckeDyadic InverseMoment InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge HeckeInverseAmplification

theorem polynomial_clipped_energy {ι : Type*} (rows : Finset ι)
    (χ : ι→Character) (inv : Bool) (A : ι→ℂ)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c θ D E : ℝ) (J : ℕ) (hc : 0<c) (hD : 0<D) (hE : 0≤E)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W (c*y)=W (c*y))
    (he : ∀s, (∑i∈rows,‖polynomial (χ i) inv (childLogTest Wref s) D 0 0*A i‖^2)
      ≤E*(1+‖s‖)^(2*J)) :
    (∑i∈rows,‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)≤
      E*(1+‖θ‖)^(2*J)*
        (∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) v‖)^2 := by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let B:=density g (Real.log c)
  let φ : rows→ℝ→ℂ:=fun i v=>polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i
  have hint (i : rows) : Integrable (fun v:ℝ=>B v*φ i v) := by
    simpa only [B,φ,mul_assoc] using
      (polynomial_mode_integrable (χ i) inv g Wref b c θ D hD hWref).mul_const (A i)
  have hbound (v : ℝ) : (∑i:rows,‖φ i v‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖v‖)^J)^2 := by
    dsimp only [φ]
    rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (childLogTest Wref (θ+v)) D 0 0*A i‖^2)]
    apply (he (θ+v)).trans
    have hh : 1+‖θ+v‖≤(1+‖θ‖)*(1+‖v‖) := by
      have hn:=norm_add_le θ v
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg v)]
    calc
      _≤E*((1+‖θ‖)*(1+‖v‖))^(2*J):=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden : Integrable (fun v:ℝ=>(1+‖v‖)^J*‖B v‖) := by
    simpa only [B,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy B φ
    (fun v:ℝ=>(1+‖v‖)^J) (by intro v;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq (i : rows) : (∫v:ℝ,B v*φ i v)=
      polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i := by
    rw [polynomial_clipped_fourier (χ i) inv W lo hi hlo hs hW Wref b c θ D hc hD hWref hagree,
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards with v
    dsimp [B,φ,g]
    ring
  simp_rw [heq] at hh
  rw [Finset.sum_coe_sort rows (fun i=>‖polynomial (χ i) inv (clippedTest W c θ) D 0 0*A i‖^2)] at hh
  simpa only [B,density_norm,g] using hh

theorem rawMoment_reference (data : RowData)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Wref : ℝ→ℂ) (b c κ C : ℝ) (J : ℕ) (hC : 0≤C)
    (hWref : ∀x,Wref x≠0 → x≤b)
    (hagree : ∀y,0<y → Wref y*W y=W y)
    (he : ∀s,RawMoment data (childLogTest Wref s) c κ (C*(1+‖s‖)^(2*J))) :
    RawMoment data W c κ
      (C*(∫v:ℝ,(1+‖v‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) v‖)^2) := by
  intro H D hH hD hHD rows hrows
  have hh:=polynomial_clipped_energy rows data.character true (fun _=>1)
    W lo hi hlo hs hW Wref b 1 0 D (C*H*(H*max 1 D)^κ) J (by norm_num) hD
    (by positivity) hWref (by simpa only [one_mul] using hagree) (by
      intro s
      have hb:=he s H D hH hD hHD rows hrows
      simpa only [mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hb)
  have heq : clippedTest W 1 0=W := by
    funext x
    simp [clippedTest,childLogTest,logPhase]
  rw [heq] at hh
  simpa only [mul_one,one_mul,norm_zero,add_zero,one_pow,mul_assoc,mul_left_comm,mul_comm] using hh

end SevenEighths.DetectorDictionaryInverseRawFourier

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Dictionary.InverseRawCompact -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawCompact
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment FourierBridge HeckePrimeAnnular
open CenteredMomentOriginalReflectionErrorMass CenteredMomentCounting
open ActualEisensteinCubic ConcreteTraceCRT

local notation "O" => HeckeFamily.O

lemma inverse_polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ true W D 0 freq =
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he : (∑'I:HeckeDyadic.NonzeroIdeal,coefficient χ true I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [coefficient_zero,zero_mul])
  simpa only [summand,HeckeDyadic.norm,annularWeight,mul_assoc] using he

theorem inverse_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ true W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [inverse_polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change coefficient χ true (0:Ideal O)*_ = 0
      rw [coefficient_zero,zero_mul])
    (by
      intro I
      by_cases hI:I=0
      · subst I
        simpa only [coefficient_zero,zero_mul,norm_zero] using hB
      rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
      exact (mul_le_mul (coefficient_norm_le χ true I) (hW _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul B))
    (by
      intro I hne
      have hw : W ((I.absNorm:ℝ)/D)≠0 := by
        intro hz
        exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
      exact ((div_le_iff₀ hD).mp (hs hw)).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))
  convert hh using 1; ring

lemma childLogTest_norm (W : ℝ→ℂ) (s x : ℝ) :
    ‖childLogTest W s x‖=‖W x‖ := by
  simp only [childLogTest,norm_mul,logPhase_norm,mul_one]

theorem inverse_reference_bound (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃A:ℝ,0<A ∧ ∀(χ:Character) (s D:ℝ),0<D →
      ‖polynomial χ true (childLogTest W s) D 0 0‖≤A*Real.sqrt D := by
  obtain ⟨B,hB,hbound⟩:=compact_norm_bound W a b ha hs W.continuous
  refine ⟨128*max 1 b*B,by positivity,?_⟩
  intro χ s D hD
  apply inverse_polynomial_bound χ (childLogTest W s) b B D 0 hB.le hD
  · intro x
    simpa only [childLogTest_norm] using hbound x
  · intro x hx
    have hw : W x≠0 := by
      intro hz
      exact hx (by simp only [childLogTest,hz,zero_mul])
    exact (hs hw).2

theorem nonzero_element_rows_card (rows : Finset NonzeroElement) (H : ℝ) (hH : 1≤H)
    (hrows : ∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) :
    (rows.card:ℝ)≤128*H := by
  have hh:=DescentFiberCost.finite_element_count_real (rows.image Subtype.val) H hH (by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrows v hv)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem reference_energy_linear (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃K:ℝ,0<K ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤K*H*D := by
  obtain ⟨A,hA,hbound⟩:=inverse_reference_bound W a b ha hs
  refine ⟨128*A^2,by positivity,?_⟩
  intro χ rows s H D hH hD hrows
  calc
    _≤∑v∈rows,A^2*D := by
      apply Finset.sum_le_sum
      intro v _
      have hh:=pow_le_pow_left₀ (norm_nonneg _) (hbound (χ v) s D hD) 2
      simpa only [mul_pow,Real.sq_sqrt hD.le] using hh
    _=(rows.card:ℝ)*(A^2*D) := by simp
    _≤(128*H)*(A^2*D) := mul_le_mul_of_nonneg_right
      (nonzero_element_rows_card rows H hH hrows) (by positivity)
    _=(128*A^2)*H*D := by ring

theorem subunit_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃C0:ℝ,0<C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D → D≤1 →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K,hK,?_⟩
  intro χ rows s H D hH hD hD1 hrows
  exact (hbound χ rows s H D hH hD hrows).trans
    (mul_le_of_le_one_right (by positivity) hD1)

lemma scale_le_rows (c H D : ℝ) (hc : 0≤ c) (hH : 1≤H)
    (_hD : 0<D) (hDH : D^(1+c)≤H) : D≤H := by
  by_cases hD1:D≤1
  · exact hD1.trans hH
  · have hd : 1≤D := le_of_not_ge hD1
    calc
      D=D^(1:ℝ) := (Real.rpow_one D).symm
      _≤D^(1+c) := Real.rpow_le_rpow_of_exponent_le hd (by linarith)
      _≤H := hDH

theorem small_rows_reference_energy (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D c:ℝ),1≤H → H≤H0 → 0≤ c → 0<D → D^(1+c)≤H →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤C0*H := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro χ rows s H D c hH hHH0 hc hD hDH hrows
  calc
    _≤K*H*D := hbound χ rows s H D hH hD hrows
    _≤K*H*H0 := mul_le_mul_of_nonneg_left ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
      (by positivity)
    _=(K*H0)*H := by ring

lemma raw_majorant_ge_linear (C C0 H D κ s : ℝ) (J : ℕ)
    (hC : 0≤C) (hC0 : 0≤C0) (hH : 1≤H) (hκ : 0≤κ) :
    C0*H≤((C+C0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
  have ht : 1≤(1+‖s‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg s])
  have hb : 1≤H*max 1 D := hH.trans
    (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
  have hp : 1≤(H*max 1 D)^κ := Real.one_le_rpow hb hκ
  calc
    C0*H≤(C+C0)*H := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _≤((C+C0)*(1+‖s‖)^(2*J))*H := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) ht) (by positivity)
    _≤_ := le_mul_of_one_le_right (by positivity) hp

theorem rawMoment_of_large_rows_ge_one (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤ c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 1≤D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro data c κ C J hc hκ hC hlarge s H D hH hD hDH rows hrows
  have hsmall (hDH0:D≤H0) :
      (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
        ((C+K*H0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
    calc
      _≤K*H*D := hbound data.character rows s H D hH hD hrows
      _≤K*H*H0 := mul_le_mul_of_nonneg_left hDH0 (by positivity)
      _=(K*H0)*H := by ring
      _≤_ := raw_majorant_ge_linear C (K*H0) H D κ s J hC (by positivity) hH hκ
  by_cases hHH0:H≤H0
  · exact hsmall ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
  by_cases hD1:D≤1
  · exact hsmall (hD1.trans hH0)
  · apply (hlarge s H D (le_of_not_ge hHH0) (le_of_not_ge hD1) hDH rows hrows).trans
    gcongr
    exact le_add_of_nonneg_right (by positivity)

theorem rawMoment_of_large_rows (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤ c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 0<D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨C0,hC0,hcomplete⟩:=rawMoment_of_large_rows_ge_one W a b ha hs H0 hH0
  refine ⟨C0,hC0,?_⟩
  intro data c κ C J hc hκ hC hlarge
  apply hcomplete data c κ C J hc hκ hC
  intro s H D hH hD hDH rows hrows
  exact hlarge s H D hH (zero_lt_one.trans_le hD) hDH rows hrows

end SevenEighths.DetectorDictionaryInverseRawCompact

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Dictionary.InverseRawGeometry -/

section

namespace OAI

noncomputable section
namespace SevenEighths.DetectorDictionaryInverseRawGeometry
open InverseMoment InverseInitialCanonicalState

def capacityGap (c : ℝ) : ℝ:=c/(1+c)

theorem capacityGap_pos (c : ℝ) (hc : 0<c) : 0<capacityGap c :=
  div_pos hc (by linarith)

theorem capacityGap_lt_one (c : ℝ) (hc : 0<c) : capacityGap c<1 := by
  apply (div_lt_one (by linarith : 0<1+c)).mpr
  linarith

theorem raw_log_capacity (H D c : ℝ) (hH : 1<H) (hD : 1≤D) (hc : 0<c)
    (hcap : D^(1+c)≤H) :
    0≤Real.logb H D ∧ Real.logb H D≤1-capacityGap c ∧
    2*Real.logb H D≤3-capacityGap c ∧ H^(Real.logb H D)=D := by
  have hHp : 0<H:=zero_lt_one.trans hH
  have hDp : 0<D:=zero_lt_one.trans_le hD
  have hlogH : 0<Real.log H:=Real.log_pos hH
  have hh:=Real.log_le_log (Real.rpow_pos_of_pos hDp (1+c)) hcap
  rw [Real.log_rpow hDp] at hh
  have hr : Real.logb H D≤1/(1+c) := by
    unfold Real.logb
    apply (le_div_iff₀ (by linarith : 0<1+c)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogH).mpr
    simpa only [mul_div_assoc,mul_comm,mul_left_comm,one_mul] using hh
  have he : 1/(1+c)=1-capacityGap c := by
    unfold capacityGap
    field_simp
    ring
  have hg:=(capacityGap_pos c hc).le
  exact ⟨div_nonneg (Real.log_nonneg hD) hlogH.le,hr.trans_eq he,
    by linarith [hr.trans_eq he],Real.rpow_logb hHp (ne_of_gt hH) hDp⟩

theorem raw_fixed_reserves (c κ : ℝ) (hc : 0<c) (hκ : 0<κ) :
    ∃η τ π ε : ℝ,0<η ∧ 0<τ ∧ 0<π ∧ 0<ε ∧
      η≤1 ∧ η≤ capacityGap c/200 ∧ τ≤ capacityGap c/200 ∧
      40*η+π+ε≤κ := by
  let η:=min (capacityGap c/200) (min (κ/100) (1/100))
  have hg:=capacityGap_pos c hc
  have hη : 0<η:=lt_min (by positivity)
    (lt_min (by positivity) (by norm_num))
  have hηg : η≤ capacityGap c/200:=min_le_left _ _
  have hηκ : η≤κ/100:=(min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η≤1/100:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,η,κ/4,κ/4,hη,hη,by positivity,by positivity,by linarith,hηg,hηg,?_⟩
  linarith

theorem raw_retained_margins (H D c B θ v Hfreq η τ Q : ℝ)
    (hH : 1<H) (hD : 1≤D) (hc : 0<c) (hcap : D^(1+c)≤H)
    (hP : -2*η≤B-θ) (hQ : Q≤B-θ+3*η) (hη : 0≤η)
    (hηsmall : η≤ capacityGap c/100) (hτ : τ≤ capacityGap c/100)
    (hcut : InverseInitialProfile.radialCenter 1 Hfreq θ (Real.logb H D) B≤4*η+τ) :
    CanonicalMargins
      (max 0 (Real.logb H D-B-v)+(θ+v+2*η)) (θ+Hfreq+2*η) Q 0
      (3*capacityGap c/4) := by
  obtain ⟨hr,hfirst,hsecond,_⟩:=raw_log_capacity H D c hH hD hc hcap
  have hh:=enlarged_initial_margins 1 (Real.logb H D) 0 0 B θ v Hfreq η τ Q
    (capacityGap c) (capacityGap c)
    (by simpa using hfirst) (by simpa using hsecond) (by norm_num) hP
    (by simpa using hQ) (by simpa using (capacityGap_pos c hc).le) hη
    (by simpa using hηsmall) (by simpa using hτ) (by simpa using hcut)
  simpa using hh

theorem raw_output_budget (H D κ e : ℝ) (hH : 1≤H) (hκ : 0≤κ) (he : e≤κ) :
    H^(1+e)≤H*(H*max 1 D)^κ := by
  have hHp : 0<H:=zero_lt_one.trans_le hH
  rw [Real.rpow_add hHp,Real.rpow_one]
  apply mul_le_mul_of_nonneg_left _ hHp.le
  calc
    H^e≤H^κ:=Real.rpow_le_rpow_of_exponent_le hH he
    _≤(H*max 1 D)^κ:=Real.rpow_le_rpow hHp.le (by nlinarith [le_max_left 1 D]) hκ

end SevenEighths.DetectorDictionaryInverseRawGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap InverseInitialExcludedPolynomial
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge UniqueFactorizationMonoid IdealMobiusDivisorSum
open DetectorDictionaryInverseRawGeometry
local notation "O"=>HeckeFamily.O

def basePeriod (data:RowData):ℕ:=(baseCharacter data).period

def excluded (data:RowData):Finset (Ideal O):=reflectionExcludedPrimes (basePeriod data)

def deletedBase (data:RowData):Character:=
  (baseCharacter data).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data))

theorem basePeriod_ne_zero (data:RowData):basePeriod data≠0:=Nat.ne_of_gt (Character.period_pos _)

theorem basePeriod_le (data:RowData):Ideal.span {(basePeriod data:O)}≤(baseCharacter data).modulus:=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Character.period_mem _))

theorem raw_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (idealCoeff (deletedBase data)).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (idealCoeff (deletedBase data)).toMonoidHom):=
  deleted_physical_base_gates (baseCharacter data) (basePeriod data)
    (basePeriod_ne_zero data) (basePeriod_le data)

theorem actual_row_fixed_base (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff (data.character u) I=idealCoeff (baseCharacter data) I*idealRowHom u.val I:=by
  rw [baseCharacter_coeff]
  exact fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u) I

theorem actual_deleted_row (data:RowData)(u:NonzeroElement)(I:Ideal O):
    idealCoeff ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) I=
      idealCoeff (deletedBase data) I*idealRowHom u.val I:=by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,idealCoeff_excludePrimes,actual_row_fixed_base]
  split_ifs <;> simp

def completeCutoff (H b Btree cap:ℝ):ℕ:=⌈max (Btree*H^(cap+1)) (b*H)⌉₊

theorem completeCutoff_tree (H b Btree cap:ℝ):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ):=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem completeCutoff_columns (H b Btree cap D n:ℝ)(hb:0≤b)(hD:0≤D)
    (hDH:D≤H)(hn:1≤n):b*(D/n)≤(completeCutoff H b Btree cap:ℝ):=by
  have hn0:0<n:=zero_lt_one.trans_le hn
  have hdn:D/n≤D:=(div_le_iff₀ hn0).mpr (le_mul_of_one_le_right hD hn)
  exact (mul_le_mul_of_nonneg_left (hdn.trans hDH) hb).trans
    ((le_max_right _ _).trans (Nat.le_ceil _))

theorem excluded_divisor_norm (data:RowData)(j:Ideal O)
    (hj:j∈idealDivisors (∏P∈excluded data,P)):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤((∏P∈excluded data,P).absNorm:ℝ):=by
  have hP:Squarefree (∏P∈excluded data,P):=
    prime_product_squarefree _ (reflectionExcludedPrimes_prime (basePeriod data))
  have hd: j∣∏P∈excluded data,P:=(mem_idealDivisors hP.ne_zero).mp hj
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hd
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)) (map_dvd Ideal.absNorm hd)

theorem shifted_raw_geometry_eventually (data:RowData)(c eta:ℝ)(hc:0<c)(heta:0<eta):
    ∀ᶠH:ℝ in atTop,1<H ∧ ∀D:ℝ,1≤D→D^(1+c)≤H→
      ∀j∈idealDivisors (∏P∈excluded data,P),
      let r:=Real.logb H (D/(j.absNorm:ℝ));
      -eta≤ r ∧ r≤1-capacityGap c ∧ 2*r≤3-capacityGap c ∧
      H^r=D/(j.absNorm:ℝ) ∧ r+7*eta≤1+7*eta ∧ D≤H:=by
  have ht:∀ᶠH:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤H^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with H hH ht
  refine ⟨hH,?_⟩
  intro D hD hcap j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  obtain ⟨hr0,hr1,hr2,hex⟩:=raw_log_capacity H D c hH hD hc hcap
  have hr:r=Real.logb H D-Real.logb H (j.absNorm:ℝ):=
    Real.logb_div hD0.ne' hn0.ne'
  have hnlog:0≤Real.logb H (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hH).le
  have hneta:Real.logb H (j.absNorm:ℝ)≤eta:=by
    exact (Real.logb_le_iff_le_rpow hH hn0).mpr (hnB.trans ht)
  have hrlo:-eta≤ r:=by rw [hr];linarith
  have hrup:r≤1-capacityGap c:=by rw [hr];linarith
  refine ⟨hrlo,hrup,by rw [hr];linarith,
    Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0),?_,?_⟩
  · linarith [(capacityGap_pos c hc).le]
  · calc
      D=H^(Real.logb H D):=hex.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _

theorem deleted_row_complete_polynomial (data:RowData)(u:NonzeroElement)
    (W:ℝ→ℂ)(H r sigma freq b:ℝ)(hH:0<H)
    (hW:∀x,W x≠0→x≤b)(Dpool:ℕ)(hbudget:b*H^r≤(Dpool:ℝ)):
    polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (H^r) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H r 0 u.val:=by
  let χ:=(data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))
  let F:=InitialMeanSquare.outsideSquarefreeIdeals (excluded data) Dpool
  have hs:(∑'I:Ideal O,(moebius I:ℂ)*idealCoeff χ I*
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)))=
      ∑I∈F,(moebius I:ℂ)*idealCoeff χ I*
        (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-HeckeDyadic.shift sigma freq)):=by
    apply tsum_eq_sum
    intro I hn
    by_cases hsq:Squarefree I
    · by_cases hout:outside (excluded data) I
      · by_cases hw:W ((I.absNorm:ℝ)/H^r)=0
        · simp only [hw,zero_mul,mul_zero]
        · have hN:(I.absNorm:ℝ)≤(Dpool:ℝ):=
            ((div_le_iff₀ (Real.rpow_pos_of_pos hH r)).mp (hW _ hw)).trans hbudget
          have hmem:I∈F:=by
            apply Finset.mem_filter.mpr
            refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hsq⟩
            · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hsq.ne_zero)
            · exact_mod_cast hN
          exact False.elim (hn hmem)
      · have hz:=deleted_zero_outside (data.character u) (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data)) I hout
        simp only [χ,hz,mul_zero,zero_mul]
    · simp only [moebius_of_not_squarefree hsq,Int.cast_zero,zero_mul]
  rw [polynomial_all_ideals,hs,normalization_eq H r hH]
  unfold InverseInitialConjugateEnergy.originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [actual_deleted_row]
  simp only [twistedProfile,InverseInitialPoissonBridge.heckeIdealCharacter_apply]
  change (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq)) =
    (moebius I:ℂ) * (idealCoeff (deletedBase data) I * idealRowHom u.val I) *
      (W ((I.absNorm:ℝ)/H^r)*(((I.absNorm:ℝ)/H^r:ℝ):ℂ)^(-shift sigma freq))
  ring

theorem raw_complete_pool (data:RowData)(H D c b Btree cap:ℝ)
    (hH:1<H)(hD:1≤D)(hc:0<c)(hcap:D^(1+c)≤H)(hb:0≤b)
    (W:ℝ→ℂ)(hW:∀x,W x≠0→x≤b):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ) ∧
    ∀j∈idealDivisors (∏P∈excluded data,P),∀u:NonzeroElement,∀sigma freq:ℝ,
      polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W
        (D/(j.absNorm:ℝ)) sigma freq=
      InverseInitialConjugateEnergy.originalTotalPolynomial
        (InitialMeanSquare.outsideSquarefreeIdeals (excluded data)
          (completeCutoff H b Btree cap)) 1
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
        (twistedProfile W sigma freq) H (Real.logb H (D/(j.absNorm:ℝ))) 0 u.val:=by
  refine ⟨completeCutoff_tree _ _ _ _,?_⟩
  intro j hj u sigma freq
  have hn:= (excluded_divisor_norm data j hj).1
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hex:=Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0)
  obtain ⟨_,hr,_,heD⟩:=raw_log_capacity H D c hH hD hc hcap
  have hDH:D≤H:=by
    calc
      D=H^(Real.logb H D):=heD.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le
        (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _
  have hbudget:b*H^(Real.logb H (D/(j.absNorm:ℝ)))≤
      (completeCutoff H b Btree cap:ℝ):=by
    rw [hex]
    exact completeCutoff_columns H b Btree cap D _ hb hD0.le hDH hn
  simpa only [hex] using deleted_row_complete_polynomial data u W H
    (Real.logb H (D/(j.absNorm:ℝ))) sigma freq b hH0 hW _ hbudget

end SevenEighths.DetectorDictionaryInverseRawInitialGates

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseInitialExcludedOverlap InverseMoment InverseInitialProfile
local notation "O"=>HeckeFamily.O

theorem conjugate_element_apply (η:Ideal O→*ℂ)(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors (η:Ideal O→*ℂ)(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)

theorem conjugate_element_norm (η:Ideal O→*ℂ)(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]

theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  exact hn x

theorem raw_conjugate_zero_outside (data:RowData)(I:Ideal O)
    (hI:¬outside (excluded data) I):
    conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom I=0:=by
  change star (idealCoeff (deletedBase data) I)=0
  rw [show idealCoeff (deletedBase data) I=0 from
    deleted_zero_outside (InverseInitialDetectorSource.baseCharacter data)
      (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) I hI,star_zero]

theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring

theorem childLogTest_conjugate_norm (W:ℝ→ℂ)(θ x:ℝ):
    ‖childLogTest (fun x=>star (W x)) (-θ) x‖=‖W x‖:=by
  rw [InverseInitialProfileBounds.childLogTest_norm,norm_star]

theorem childLogTest_physical_profiles (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=clippedSource (fun x=>star (W x)) 1 (-θ) ∧
    childLogTest W θ=clippedSource W 1 θ:=by
  rw [childLogTest_conjugate]
  exact ⟨InverseInitialProfileBounds.childLogTest_eq_clipped _ _,
    InverseInitialProfileBounds.childLogTest_eq_clipped _ _⟩

end SevenEighths.DetectorDictionaryInverseRawConjugateGates

end

end OAI

end

