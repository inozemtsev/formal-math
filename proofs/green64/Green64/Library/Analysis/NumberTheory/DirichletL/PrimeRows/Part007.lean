module

public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part019

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / PrimeRows / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubeErrorSaving -/

section

namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem original_row_cube_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((17/2:ℝ)+saving)/τ)
  have hN' : (17/2:ℝ)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := central_source_crude_scale hZ (by linarith : 0≤a) he.le
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(17/2:ℝ)/Z^(τ*N)≤Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/height H^N) := by
      have hh : Z^(13/2:ℝ)*Z^(2:ℝ)=Z^(17/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError -/

section

namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def finiteCentralCubeRows {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e : ℝ) (a H : FreeRow→ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    centralCubeIntegral S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
      η u W0 W1 X Y Z (a u) e (H u)

theorem finite_cube_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48) (hA : 0≤A)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_cube_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((13/16:ℝ)+ζ)≤Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (13/16:ℝ)+ζ≤1 by linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (1/6:ℝ)≤1 by norm_num)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (a u) e (H u)‖≤E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralCubeRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (a u) e (H u)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def cubeWeightedRow {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : HeightSpace→ℂ :=
  {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
    (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50))

theorem cubeWeightedRow_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H) heightMeasure := by
  have hi := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  have hE : MeasurableSet E := ((measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.2|) by fun_prop) measurable_const)
  apply (integrable_indicator_iff hE).mpr
  have heq : weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)=
      fun t=>(∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) t := by
    funext t
    exact weightedRowOnLines_eq ..
  rw [heq]
  exact (hi.mono_set (fun t ht=>ht.1.1)).const_mul _

lemma cubeWeightedRow_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H t ∂heightMeasure)=
      (∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H := by
  have hE : MeasurableSet {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H} :=
    ((measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
      (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)).inter
      (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.2|) by fun_prop) measurable_const)
  unfold cubeWeightedRow
  rw [integral_indicator hE]
  simp_rw [weightedRowOnLines_eq]
  rw [integral_const_mul]
  unfold centralCubeIntegral
  ring

theorem finiteCentralCubeRows_eq_integral {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
      detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      cubeWeightedRow S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z (a u) e (H u) t
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  let f (u : FreeRow) (P : ∀i,T i) := cubeWeightedRow S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z (a u) e (H u)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    rcases hbin u hu with ⟨ha,ha',hB,hH,hzero⟩
    exact cubeWeightedRow_integrable e (a u) (B u) (H u) (idx u) he he' ha ha' hB hH
      S hS hmax hfirst _ _ η u (hR u hu) (ψ u) hzero W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P _=>hi u hu P)
  refine ⟨integrable_finsetSum _ hiu,?_⟩
  change finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu,Finset.mul_sum]
  unfold finiteCentralCubeRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=>hi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  exact (cubeWeightedRow_integral S hS hmax _ _ η u W Yp W0 W1 X Y Z (a u) e (H u)).symm

lemma cube_buffered_heights (t : HeightSpace) (H B : ℝ) (i : ℕ)
    (ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H) (hB : 0≤B)
    (hbuffer : H+B/2≤(3*i+2:ℕ)*B) :
    |t.1.1|≤(3*i+2:ℕ)*B ∧ |t.2|≤(3*i+2:ℕ)*B ∧
      |t.1.2|+B/2≤(3*i+2:ℕ)*B := by
  constructor
  · linarith [ht.1.1]
  constructor
  · linarith [ht.1.2]
  · linarith [ht.2]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeReduction -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem canonical_probe_minus_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (51/100:ℝ)≤alpha u ∧ alpha u≤1 ∧ 2<base u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u)<alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨C0,hC0,h0⟩ := canonical_probe_minus_central K e δ a b B ζ saving he he' hδ hδ' hζ ha hb hB hβ
    S hS hmax (hfirst.mono_parameter (by linarith)) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ B hτ hb hζ' hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis length hl0 hl hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis length hl0 hl W hWS hWB
  let R := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis length hl hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)
  have hE : 0≤E := by dsimp [E];positivity
  have hsave : Z^(-saving)≤E := by dsimp [E];have : 0≤Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem exists_source_cube_bins (e B : ℝ) (he : 0<e) (hB : 2<B)
    (n : ℕ) (hn : 0<n) (hwidth : (49/100:ℝ)≤n*e)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (ψ : FreeRow→ι→Character) :
    ∃idx grid : FreeRow→ℕ,∀u : FreeRow,
      1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
      let a : ℝ := 51/100+e*grid u
      let H : ℝ := (3*idx u+1:ℕ)*B
      (51/100:ℝ)≤a ∧ a≤1 ∧ B≤H ∧ H+B/2≤(3*idx u+2:ℕ)*B ∧
      a≤detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*idx u*B) ∧
      detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*idx u*B)<a+e ∧
      detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*(idx u+1:ℕ)*B)<a+2*e ∧
      (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS η u (ψ u) j) s=0 ∧
        ¬((sourceDetectorFamily S hS η u (ψ u) j).residue=1 ∧ s=1) ∧
        a≤ s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*B) := by
  have hex (u : FreeRow) := exists_detector_buffered_bin (sourceDetectorFamily S hS η u (ψ u)) B e hB he n hn hwidth
  choose idx grid hspec using hex
  refine ⟨idx,grid,?_⟩
  intro u
  rcases hspec u with ⟨hi,hin,ha,hlo,hhi,hnext,hzero,hdisk⟩
  refine ⟨hi,hin,?_,?_,ha,?_,?_,hlo,hhi,hnext,hzero⟩
  · apply Nat.le_floor
    apply (le_div_iff₀ he).mpr
    nlinarith
  · nlinarith [Nat.cast_nonneg (α:=ℝ) (grid u)]
  · push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (idx u)]
  · push_cast
    linarith

theorem exists_source_cube_bin_number (e : ℝ) (he : 0<e) :
    ∃n : ℕ,0<n ∧ (49/100:ℝ)≤n*e := by
  refine ⟨⌈(49/100:ℝ)/e⌉₊+1,by omega,?_⟩
  have hh := Nat.le_ceil ((49/100:ℝ)/e)
  have hmul := (div_le_iff₀ he).mp hh
  push_cast
  nlinarith

theorem source_cube_height_eventually (τ : ℝ) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ 2<Z^τ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeChoice -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem canonical_probe_exists_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀(η : Character) (Z : ℝ),1≤Z → 2<Z^τ →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀ψ : FreeRow→ι→Character,∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (ψ u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (ψ u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,hbound⟩ := canonical_probe_minus_cube (ι:=ι) K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha hb hB hβ S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨n,hn,hwidth⟩ := exists_source_cube_bin_number e he
  refine ⟨C,hC,n,hn,?_⟩
  intro η Z hZ hZT T hT hdis length hl0 hl hpool W hWS hWB ψ
  obtain ⟨idx,grid,hbins⟩ := exists_source_cube_bins e (Z^τ) he hZT n hn hwidth S hS.prime η ψ
  refine ⟨idx,grid,?_,?_,?_⟩
  · intro u
    exact ⟨(hbins u).1,(hbins u).2.1,(hbins u).2.2.1,(hbins u).2.2.2.2.2.2.1⟩
  · intro u
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    exact ⟨ha0,ha1,hlo,hhi,hnext,hzero⟩
  · apply hbound η Z hZ T hT hdis length hl0 hl hpool W hWS hWB
      (fun u=>51/100+e*grid u) (fun _=>Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx ψ
    intro u hu
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    refine ⟨ha0,ha1,hZT,hBH,?_,hnext⟩
    have : 0≤Z^τ := Real.rpow_nonneg (by linarith) _
    linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrincipalMellinGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Complex Set
namespace SevenEighths.PrincipalMellinGrowth
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary

def principalConstant (M : Ideal HeckeFamily.O) : ℝ :=
  (1+HeckeLogarithmicInput.uniformConstant)*(M.absNorm : ℝ)^(3/5 : ℝ)*
    HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport M).card

theorem principalConstant_pos (M : Ideal HeckeFamily.O) [NeZero M] :
    0<principalConstant M := by
  have hQ : 0<(M.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  exact mul_pos (mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg])
    (Real.rpow_pos_of_pos hQ _)) (pow_pos (HeckeDeletionBounds.localBound_pos (by norm_num)) _)

lemma poleRemoved_eq_mul_regular (χ : Character) (hχ : χ.residue=1)
    {s : ℂ} (hs : s+1≠0) :
    HeckeOrigin.poleRemoved χ s=(s+1)*HeckeLogarithmicInput.regular χ s := by
  simp only [HeckeLogarithmicInput.regular,ite_eq_left hχ,HeckePrincipalStrip.sourceNormalized]
  field_simp

theorem principal_poleRemoved_growth (χ : Character) (hχ : χ.residue=1)
    {s : ℂ} (hs : (19/20 : ℝ)≤ s.re) :
    ‖HeckeOrigin.poleRemoved χ s‖≤principalConstant χ.modulus*‖s+1‖*(3+|s.im|)^2 := by
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue=1 := (HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mp hχ
  have hs0 : 0<s.re := by linarith
  have h0 : s≠0 := by intro hh; norm_num [hh] at hs
  have hplus : s+1≠0 := by
    intro hh
    have hr := congrArg Complex.re hh
    simp only [add_re,one_re,zero_re] at hr
    linarith
  have heq : HeckeOrigin.poleRemoved χ s=
      ((s+1)*HeckeLogarithmicInput.regular ψ s)*HeckeFiniteDeletion.factors χ.modulus ψ s := by
    rw [← poleRemoved_eq_mul_regular ψ hψ hplus]
    by_cases h1 : s=1
    · subst s
      rw [HeckeOrigin.poleRemoved_one,HeckeOrigin.poleRemoved_one]
      exact HeckeFiniteDeletion.regularizedL_eq_of_mask χ ψ hmask (by norm_num)
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1,HeckeOrigin.poleRemoved_eq ψ h0 h1,
        HeckeFiniteDeletion.LFunction_eq_of_mask χ ψ hmask hs0 h1]
      ring
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10 : ℝ)≤ s.re)
  have hd := (HeckeDeletionBounds.factors_bound_pow (19/20) (by norm_num)
    χ.modulus ψ hs).1
  have hQ' : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)≤(χ.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hC := HeckeLogarithmicInput.uniformConstant_nonneg
  have hD := (HeckeDeletionBounds.localBound_pos (by norm_num : (0 : ℝ)<19/20)).le
  rw [heq,norm_mul,norm_mul]
  calc
    _ ≤ (‖s+1‖*(HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
          (3+|s.im|)^2))*
        HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport χ.modulus).card := by
      gcongr
    _ ≤ (‖s+1‖*((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
          (3+|s.im|)^2))*
        HeckeDeletionBounds.localBound (19/20)^(IdealMobiusDivisorSum.primeSupport χ.modulus).card := by
      gcongr
      linarith
    _ = _ := by unfold principalConstant; ring

def wAmplitude (M : Ideal HeckeFamily.O) (cw : ℝ) : ℝ := 9*(cw+2)*principalConstant M

def zAmplitude (M : Ideal HeckeFamily.O) : ℝ := 216*principalConstant M

theorem wAmplitude_pos (M : Ideal HeckeFamily.O) [NeZero M] {cw : ℝ} (hcw : 1<cw) :
    0<wAmplitude M cw := by
  unfold wAmplitude
  exact mul_pos (mul_pos (by norm_num) (by linarith)) (principalConstant_pos M)

theorem zAmplitude_pos (M : Ideal HeckeFamily.O) [NeZero M] : 0<zAmplitude M := by
  unfold zAmplitude
  exact mul_pos (by norm_num) (principalConstant_pos M)

theorem fixed_principal_w_growth (M : Ideal HeckeFamily.O) [NeZero M]
    {cw : ℝ} (hcw : 1<cw) {x : ℝ} (hx : x∈Icc (19/20 : ℝ) cw) (t : ℝ) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤wAmplitude M cw*height t^3 := by
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(((x:ℂ)+t*I) : ℂ).re by simpa using hx.1)
  have hn : ‖((x:ℂ)+t*I)+1‖≤(cw+2)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
      mul_zero,sub_zero,add_zero,zero_add,mul_one,one_re,one_im]
    rw [abs_of_pos (by linarith [hx.1] : 0<x+1)]
    unfold height
    have hmul : 0≤(cw+1)*|t| := mul_nonneg (by linarith) (abs_nonneg t)
    nlinarith [hx.2]
  have hheight : (3+|t|)^2≤9*height t^2 := by
    have hh : 3+|t|≤3*height t := by unfold height; linarith [abs_nonneg t]
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+|t|) hh 2
    simpa only [mul_pow,show (3:ℝ)^2=9 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have ht0 := (height_pos t).le
  change ‖HeckeOrigin.poleRemoved (fixedPrincipal M) ((x:ℂ)+t*I)‖≤
    principalConstant M*‖((x:ℂ)+t*I)+1‖*(3+|(((x:ℂ)+t*I) : ℂ).im|)^2 at hb
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  calc
    _ ≤ principalConstant M*‖((x:ℂ)+t*I)+1‖*(3+|t|)^2 := hb
    _ ≤ principalConstant M*((cw+2)*height t)*(9*height t^2) := by
      have hc2 : 0≤ cw+2 := by linarith
      gcongr
    _ = _ := by unfold wAmplitude; ring

theorem fixed_principal_z_growth (M : Ideal HeckeFamily.O) [NeZero M]
    {e : ℝ} (he : 0<e) (he' : e≤2/3) {x : ℝ}
    (hx : x∈Icc (33/200 : ℝ) (1/6+e)) (t : ℝ) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤zAmplitude M*height t^3 := by
  have hre : (6*((x:ℂ)+t*I) : ℂ).re=6*x := by simp
  have him : (6*((x:ℂ)+t*I) : ℂ).im=6*t := by simp
  have habs : |(6*((x:ℂ)+t*I) : ℂ).im|=6*|t| := by rw [him,abs_mul]; norm_num
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(6*((x:ℂ)+t*I) : ℂ).re by rw [hre]; linarith [hx.1])
  have hn : ‖(6*((x:ℂ)+t*I) : ℂ)+1‖≤6*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp only [add_re,add_im,one_re,one_im,add_zero,hre,him]
    rw [abs_of_pos (by linarith [hx.1] : 0<6*x+1),abs_mul]
    rw [abs_of_pos (by norm_num : (0:ℝ)<6)]
    unfold height
    linarith [hx.2]
  have hheight : (3+6*|t|)^2≤36*height t^2 := by
    have hh : 3+6*|t|≤6*height t := by unfold height; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+6*|t|) hh 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have ht0 := (height_pos t).le
  change ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((x:ℂ)+t*I))‖≤
    principalConstant M*‖(6*((x:ℂ)+t*I) : ℂ)+1‖*(3+|(6*((x:ℂ)+t*I) : ℂ).im|)^2 at hb
  rw [habs] at hb
  calc
    _ ≤ principalConstant M*‖(6*((x:ℂ)+t*I) : ℂ)+1‖*(3+6*|t|)^2 := hb
    _ ≤ principalConstant M*(6*height t)*(36*height t^2) := by gcongr
    _ = _ := by unfold zAmplitude; ring

theorem source_w_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ)
    (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (eta : Character) (s z : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {cw AH : ℝ}
    (hcw : 1<cw) (hAH : 0≤AH) (JH : ℕ)
    (hHB : ContinuousOn (fun w => H w z*B w z) {w : ℂ | (19/20:ℝ)≤w.re ∧ w.re≤ cw})
    (hHBbd : ∀x∈Icc (19/20:ℝ) cw, ∀t : ℝ, (x=19/20 ∨ x=cw ∨ 1≤|t|) →
      ‖H ((x:ℂ)+t*I) z * B ((x:ℂ)+t*I) z‖≤AH*height t^JH) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z eta s H B w z *
      LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply ProbeMellinBoundary.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY eta s z hEta H B
    (AL:=wAmplitude M cw) hcw hAH (wAmplitude_pos M hcw).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_w_growth M hcw hx t

theorem source_z_boundary (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (eta : Character) (s : ℂ) (hEta : LFunction eta s≠0) (H B : ℂ → ℂ → ℂ) {e AH : ℝ}
    (he : 0<e) (he' : e≤2/3) (hAH : 0≤AH) (JH : ℕ)
    (hHB : ContinuousOn (fun z => H 1 z*B 1 z)
      {z : ℂ | (33/200:ℝ)≤z.re ∧ z.re≤1/6+e})
    (hHBbd : ∀x∈Icc (33/200:ℝ) (1/6+e), ∀t : ℝ, (x=33/200 ∨ x=1/6+e ∨ 1≤|t|) →
      ‖H 1 ((x:ℂ)+t*I) * B 1 ((x:ℂ)+t*I)‖≤AH*height t^JH) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z eta s H B 1 z *
      LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ eta s hEta H B
    (AL:=zAmplitude M) he hAH (zAmplitude_pos M).le JH 3 hHB hHBbd
  intro x hx t _
  exact fixed_principal_z_growth M he he' hx t

end SevenEighths.PrincipalMellinGrowth

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductBounds
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

def localMultiplier (η : Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  (Q : ℂ)^(z-1) *
    (compensatedReplacement (coordV Q z) (coordW Q 1 w)
      (coordD Q (idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z)
      (star (idealCoeff η P.val)*(Q : ℂ)^x) ((Q : ℂ)^(-w)) /
      idealClosedCorrection η P x w z)

def selectedMultiplier (η : Character) (T : Finset PrimeIdeal) (x w z : ℂ) : ℂ :=
  ∏ P ∈ T, localMultiplier η P x w z

def slotMultiplier {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (x w z : ℂ) : ℂ :=
  ∏ j ∈ J, ∑ P ∈ T j, b j P * localMultiplier η P x w z

theorem correction_lower_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hb := (idealClosedCorrection_bound η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem correction_ne_zero (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (correction_lower_bound η S hS P hP x w z hx hw hz))

theorem correction_inverse_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hh := correction_lower_bound η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma marked_differentiableAt_w (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma marked_differentiableAt_z (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem local_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : 7/8 ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12*‖coordR Q A x z‖*(1+‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12*(1/2:ℝ)*(1+1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4*‖coordK Q η x w‖*‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4*1*(1/2:ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

lemma replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
  have hV1 : ‖1-V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have hW1 : ‖1-W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have hBq : ‖B-q‖ ≤ R+1 := (norm_sub_le B q).trans (add_le_add hB hq)
  have hVW : ‖1-V*W‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (V*W)
    rw [norm_one,norm_mul] at hn
    have hm : ‖V‖*‖W‖ ≤ 1/2 := by
      calc
        _ ≤ (1/2:ℝ)*1 := by gcongr
        _ = _ := by ring
    linarith
  have hi := inv_one_sub_norm_le_two D hD
  unfold compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (‖B-q‖*‖1-V‖*‖1-W‖*‖P‖ + ‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*P) (q*(1-V*W))
    _ ≤ ((R+1)*2*2*16+1*2)*2 := by gcongr
    _ ≤ 200*(1+R) := by linarith

def localBound (Bx Bz : ℝ) (P : PrimeIdeal) : ℝ :=
  (Ideal.absNorm P.val : ℝ)^(Bz-1) * (400*(1+(Ideal.absNorm P.val : ℝ)^Bx))

lemma localBound_nonneg (Bx Bz : ℝ) (P : PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  unfold localBound
  positivity

theorem local_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    marked_bound Q (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := correction_inverse_bound η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
  have hp : ‖(Q : ℂ)^(z-1)‖ ≤ Q^(Bz-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re,Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  change _ ≤ Q^(Bz-1)*(400*(1+Q^Bx))
  calc
    _ ≤ Q^(Bz-1)*(200*(1+Q^Bx)*2) := by gcongr
    _ = _ := by ring

def selectedBound (T : Finset PrimeIdeal) (Bx Bz : ℝ) : ℝ :=
  ∏ P ∈ T, localBound Bx Bz P

def slotBound {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : ℝ :=
  ∏ j ∈ J, ∑ P ∈ T j, ‖b j P‖ * localBound Bx Bz P

lemma selectedBound_nonneg (T : Finset PrimeIdeal) (Bx Bz : ℝ) :
    0 ≤ selectedBound T Bx Bz := Finset.prod_nonneg (fun P _ => localBound_nonneg Bx Bz P)

lemma slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (localBound_nonneg Bx Bz P))

theorem selected_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => selectedMultiplier η T x w z) {w : ℂ | 9/10 < w.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_w η S hS P (hT P hp) x z hx hz)

theorem selected_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => selectedMultiplier η T x w z) {z : ℂ | 4/25 < z.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_z η S hS P (hT P hp) x w hx hw)

theorem slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem selected_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖selectedMultiplier η T x w z‖ ≤ selectedBound T Bx Bz := by
  simp only [selectedMultiplier,selectedBound,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun P hp => local_norm_bound η S hS P (hT P hp) x w z Bx Bz hx hw hz)

theorem slot_norm_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma global_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hb := globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem combined_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (globalClosedCorrection_analytic_w η S hS x z hx hz).mul (slot_analytic_w η S hS J T b hT x z hx hz)

theorem combined_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 7/8 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (globalClosedCorrection_analytic_z η S hS x w hx hw).mul (slot_analytic_z η S hS J T b hT x w hx hw)

theorem combined_slot_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (7/8) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem selected_initial_identity (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ)
    (hx : 3/2 < x.re) (hw : 2 < w.re) (hz : 1/6 < z.re) :
    (∏ P ∈ T, (Ideal.absNorm P.val : ℂ)^(z-1)) *
      spectralCompensatedHigh S T η x w z
        (fun P => star (idealCoeff η P.val)*(Ideal.absNorm P.val : ℂ)^x)
        (fun P => (Ideal.absNorm P.val : ℂ)^(-w)) =
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w /
        LFunction (η.excludePrimes S hS.prime) x) *
        (globalClosedCorrection η S x w z * selectedMultiplier η T x w z) := by
  rw [spectralCompensatedHigh_continued S hS T hT η x w z _ _ hx hw hz]
  simp only [selectedMultiplier,localMultiplier,Finset.prod_mul_distrib,Complex.ofReal_natCast]
  ring_nf

theorem source_w_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1<cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_w η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)<w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem source_z_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : 7/8 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0<e) (he' : e≤2/3) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
        LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply PrincipalMellinGrowth.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ
    (η.excludePrimes S hS.prime) s hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) he he'
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      1 ((x : ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)

theorem source_multiplier_differentiable_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (combined_slot_analytic_w η S hS.tail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he : (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun w => ((X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z /
      LFunction (η.excludePrimes S hS.prime) s) * (Y:ℂ)^(w-1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem source_multiplier_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : 7/8 ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)<z.re at hz; linarith)
  have hH := (combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he : (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w / LFunction (η.excludePrimes S hS.prime) s) *
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

theorem source_w_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0<Y)
    (s z : ℂ) (hs : 7/8 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0) {cw : ℝ} (hcw : 1<cw) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral cw (fun w => K w z * LFunction (fixedPrincipal M) w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction (fixedPrincipal M) w) +
        K 1 z * fixedPrincipalResidue M := by
  dsimp only
  apply PrincipalMellinResidues.source_w_shift (fixedPrincipal M) _ z hcw
  · exact (source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY s z hs (by linarith)).mono (by intro w hw; change (9/10:ℝ)<w.re; linarith [hw.1])
  · exact source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1 M X Y Z hY s z hs hz hEta hcw

theorem source_residue_z_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : 7/8 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0<e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral (1/6+e) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) =
      verticalIntegral (33/200) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) +
        K 1 (1/6) * fixedPrincipalResidue M / 6 := by
  dsimp only
  apply PrincipalMellinResidues.source_residue_z_shift (fixedPrincipal M) _ he
  · exact (source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s 1 hs
      (by norm_num)).mono (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · exact source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ s hs hEta he he'

theorem local_eq_regionSlot (η : Character) (P : PrimeIdeal) (s w z : ℂ) :
    localMultiplier η P s w z = (Ideal.absNorm P.val : ℂ)^(z-1) *
      PrincipalSlotEstimate.regionSlot (Ideal.absNorm P.val)
        (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) s w z := by
  simp only [localMultiplier,PrincipalSlotEstimate.regionSlot,PrincipalSlotEstimate.regionReplacement,
    PrincipalSlotEstimate.regionMarked,idealMarkedClosed,idealClosedCorrection,Complex.ofReal_natCast]

def windowMultiplier {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (W : ι → ℝ → ℂ) (scale : ι → ℝ) (s w z : ℂ) : ℂ :=
  slotMultiplier η J T (fun j P => W j ((Ideal.absNorm P.val : ℝ)/scale j)) s w z

theorem window_at_residue {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (W : ι → ℝ → ℝ) (scale : ι → ℝ) (s : ℂ) :
    windowMultiplier η J T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      ∏ j ∈ J, ∑ P ∈ T j,
        ((W j ((Ideal.absNorm P.val : ℝ)/scale j) *
          (Ideal.absNorm P.val : ℝ)^(-(5/6 : ℝ)) : ℝ) : ℂ) *
        PrincipalSlotEstimate.principalSlot (Ideal.absNorm P.val)
          (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) s := by
  unfold windowMultiplier slotMultiplier
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro P hp
  rw [local_eq_regionSlot,PrincipalSlotEstimate.region_slot_at_residue]
  have hQ : 0 < (Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  rw [Complex.ofReal_mul,Complex.ofReal_cpow hQ.le]
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  norm_num
  ring_nf

theorem slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 7/8≤ s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(7/8 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using PrincipalSlotEstimate.weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 7/8≤ s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(7/8 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  rw [norm_mul]
  exact mul_le_mul (global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)

@[simp] theorem slotMultiplier_empty {ι : Type*} (η : Character) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (s w z : ℂ) : slotMultiplier η ∅ T b s w z = 1 := by
  simp [slotMultiplier]

theorem selected_as_slots (η : Character) (T : Finset PrimeIdeal) (s w z : ℂ) :
    selectedMultiplier η T s w z = slotMultiplier η T (fun P => {P}) (fun _ _ => 1) s w z := by
  simp [selectedMultiplier,slotMultiplier]

theorem fixed_source_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (η : Character) (s : ℂ) (hs : 7/8 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1<cw) (he : 0<e) (he' : e≤2/3) :
    let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  constructor
  · intro z hz
    exact source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY s z hs (by rw [hz]; linarith) hEta hcw
  · exact source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0
      (∏ P ∈ S, P) X Y Z hX hZ s hs hEta he he'

lemma boundary_mul_const (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

theorem fixed_source_ordered_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (η : Character) (s : ℂ) (hs : 7/8 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1<cw) (he : 0<e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hh := fixed_source_boundaries S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ η s hs hEta hcw he he'
  dsimp only at hh ⊢
  refine ⟨?_,hh.2⟩
  intro z hz
  convert boundary_mul_const _ _ _ (hh.1 z hz) (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
  funext w
  ring

theorem uniform_closed_box_bound {ι : Type*} (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (Bx Bw Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Character) (s w z : ℂ),
      s.re ∈ Icc (7/8) Bx → w.re ∈ Icc (19/20) Bw → z.re ∈ Icc (33/200) Bz →
      ‖globalClosedCorrection η S s w z * slotMultiplier η J T b s w z‖ ≤ C :=
  ⟨(3/2)*slotBound J T b Bx Bz,
    mul_nonneg (by norm_num) (slotBound_nonneg J T b Bx Bz),
    fun η s w z hs hw hz => combined_slot_bound η S hS J T b hT s w z Bx Bz hs hw.1 hz⟩

end SevenEighths.ProbeFiniteProductBounds
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FiniteProductX -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductX
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma marked_differentiableAt_x (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | 7/8 < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | 7/8 < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_x η S hS P (hT P hp) w z hw hz)

theorem slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | 7/8 < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem window_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | 7/8 < x.re} :=
  slot_analytic_x η S hS J T _ hT w z hw hz

theorem combined_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | 7/8 < x.re} :=
  (globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (selected_analytic_x η S hS T hT w z hw hz)

theorem combined_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | 7/8 < x.re} :=
  (globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (slot_analytic_x η S hS J T b hT w z hw hz)

def continuedSourceMultiplier {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(x+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((x+z-1)^2) *
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w *
      HeckeReciprocal.reciprocal (η.excludePrimes S hS) x *
      globalClosedCorrection η S x w z * slotMultiplier η J T b x w z

theorem continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (7/8 : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (7/8 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem continued_source_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a : ℝ) (w z : ℂ) :
    (fun t : ℝ => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z ((a:ℂ)+t*I) w z)
      =ᵐ[volume] (fun t : ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
        ((a:ℂ)+t*I) (globalClosedCorrection η S ((a:ℂ)+t*I))
          (slotMultiplier η J T b ((a:ℂ)+t*I)) w z) := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply continued_source_eq_raw
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem source_analytic_x_off_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (7/8 : ℝ) HeckeZeroSupremum.beta < x.re ∧ x≠1} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((Complex.isOpen_re_gt _).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (7/8 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; norm_num at hx'
  have hL := LFunction_differentiableAt (η.excludePrimes S hS.prime) hx0 (Or.inl hx.2)
  have hLn := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime) hβ (Or.inl hx.2)
  have hH := (globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : 7/8<a) (hβ : HeckeZeroSupremum.beta<a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤x.re ∧ x.re≤ c} := by
  apply (continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

theorem continued_source_principal_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (w z : ℂ)
    (hχ : (η.excludePrimes S hS).residue=1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z 1 w z=0 := by
  simp only [continuedSourceMultiplier,HeckeReciprocal.reciprocal_principal_one _ hχ,mul_zero,zero_mul]

end SevenEighths.ProbeFiniteProductX
end

end OAI

end

