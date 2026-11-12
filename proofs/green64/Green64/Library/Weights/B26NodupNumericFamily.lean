module

public import Green64.Library.Weights.Part062
public import Green64.Library.Weights.Part078

@[expose] public section

/-!
# Weights / B26NodupNumericFamily

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26NodupNumericFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The actual numerical LIST of fresh births is tested after the original
target permutation. This is stronger than freshness of its underlying set. -/
def sourceOriginalB26NumericBirthNodup434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : G) → BP g → ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (tau : BigGroupPerm (BG := G) (J+ell))
    (t : SourceOriginalB26Active434 BP J ell) : Prop :=
  (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m
    (sourceOriginalProbeMemoryPattern434 J m hmJ nu)
    (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau t)).Nodup

private theorem target_filter_family_energy
    {X I : Type} [Fintype X] [DecidableEq I]
    (pool : Finset ℕ) (family : Finset I)
    (w : X → ℝ) (hw : ∀ x,0 ≤ w x)
    (birth : I → X → Finset ℕ)
    (hbirth : ∀ i ∈ family,∀ y,birth i y ⊆ pool)
    (gate : X → Finset ℕ → Prop)
    (row : Finset ℕ → I → X → X → ℂ)
    (valid : I → X → Prop)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hPair : ∀ S ∈ pool.powerset,∀ (U : X → ℂ) (V : I → X → ℂ)
      (ET : ℝ),0 ≤ ET →
      (∀ i ∈ family,(∑ y : X,w y*‖V i y‖^2) ≤ ET) →
      ‖∑ i ∈ family,∑ x : X,
        (w x:ℂ)*star (U x)*(∑ y : X,row S i x y*V i y)‖^2 ≤
        delta*(∑ x : X,w x*‖U x‖^2)*ET)
    (f : X → Finset ℕ → ℂ) :
    sourceOriginalNumericSeenEnergy434 pool w
      (sourceOriginalNumericSeenFamilyLift434 family birth gate
        (fun S i x y => if valid i y then row S i x y else 0) f) ≤
      (delta*(family.card:ℝ))*sourceOriginalNumericSeenEnergy434 pool w f := by
  apply source_original_NUMERIC_SEEN_family_bilinear_lift434
    pool family w hw birth hbirth gate
    (fun S i x y => if valid i y then row S i x y else 0) delta hdelta
  intro S hS U V ET hET hcap
  have hcap' (i : I) (hi : i ∈ family) :
      (∑ y : X,w y*‖if valid i y then V i y else 0‖^2) ≤ ET := by
    calc
      _ ≤ ∑ y : X,w y*‖V i y‖^2 := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hv : valid i y
        · simp only [if_pos hv]
          exact le_refl _
        · simpa only [if_neg hv,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero]
            using mul_nonneg (hw y) (sq_nonneg ‖V i y‖)
      _ ≤ ET := hcap i hi
  have hh := hPair S hS U (fun i y => if valid i y then V i y else 0)
    ET hET hcap'
  simpa only [ite_mul,mul_ite,zero_mul,mul_zero] using hh

section Family
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
variable (data : SourceComparisonData434 ι G cfg x L Y Hprime)
variable (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
variable (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
variable (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
variable (c : SourceOriginalProbePattern434 G m → ℕ)
variable (theta : SourceOriginalProbePattern434 G m → ℝ)
variable (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
variable (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
variable (epsSrc epsTgt : Bool)
local notation "BP" => fun g : G => {p : ℕ // p ∈ data.Tb g}
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Nu" => SourceOriginalProbePattern434 G m

/-- The coherent sum of the numeric CLEAN comparison-error
rows in the ACTUAL physical tilted active density. Each pattern uses
its own true free-target history update and both endpoint permutations.
All four shared endpoint signs and actual birth-list Nodup are explicit. -/
def sourceOriginalB26NodupNumericComparisonFamily434
    (f : A → Finset ℕ → ℂ) (s : A) (S : Finset ℕ) : ℂ :=
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
    sourceOriginalB26NumericPermutedClean434 BP (fun _ p => p.val) J ell m hmJ nu
      mu (sigma nu) (tau nu)
      (fun a _ b => sourceOriginalB26CanonicalComparisonValue434 data.Tb data.Vbig
        J ell m hmJ nu Q (hA nu) (hB nu) xi (c nu) a b
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta (theta nu) (orientation nu) k)
      (fun t T => if sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val)
        J ell m hmJ nu (tau nu) t then f t T else 0) s S

/-- Finite coherent lifting of the genuine physical tilted B26
comparison pairing, with no change of density between steps. The
arithmetic all-pattern theorem supplies hPair in the next module.
The only extra factor is the number of probe patterns. -/
theorem source_original_B26_NODUP_NUMERIC_COMPARISON_family_energy434
    (hmu : ∀ g (p : BP g),0 ≤ physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig g p)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hPair : ∀ (U : A → ℂ) (V : Nu → A → ℂ) (ET : ℝ), 0 ≤ ET →
      (∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26ActiveEnergy434 BP J ell
          (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) (V nu) ≤ ET) →
      ‖∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
        sourceOriginalB26TiltedPermutedFullPairing434 data q N J ell m hmJ Q hA hB
          xi zeta c theta orientation k sigma tau (fun _ => U) V nu‖^2 ≤
      delta * sourceOriginalB26ActiveEnergy434 BP J ell
        (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) U * ET)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell
      (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig)
      (sourceOriginalB26NodupNumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
        hA hB xi zeta c theta orientation k sigma tau epsSrc epsTgt f) ≤
    (delta*((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ)) *
      sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell
        (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) f := by
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let w := sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let value := fun nu : Nu => fun s t : A =>
    sourceOriginalB26CanonicalComparisonValue434 data.Tb data.Vbig J ell m hmJ nu Q
      (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
  let birth := fun nu : Nu => fun t : A =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
      (fun p : Sigma BP => p.2.val)
  let gate := fun s : A => fun S : Finset ℕ =>
    (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S
  let valid := fun nu : Nu => fun t : A =>
    sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val) J ell m hmJ nu (tau nu) t
  let row := fun _S : Finset ℕ => fun nu : Nu => fun s t : A =>
    sign nu * sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) * value nu s t
  have hb (nu : Nu) (_ : nu ∈ family) (t : A) :
      birth nu t ⊆ sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val) := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨a.1,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨a.2,Finset.mem_univ _,rfl⟩⟩
  have hw (s : A) : 0 ≤ w s :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (s g i)))
  have he :
      sourceOriginalB26NodupNumericComparisonFamily434 data q N blockA blockB J ell m hmJ Q
        hA hB xi zeta c theta orientation k sigma tau epsSrc epsTgt f =
      sourceOriginalNumericSeenFamilyLift434 family birth gate
        (fun S nu s t => if valid nu t then row S nu s t else 0) f := by
    funext s S
    unfold sourceOriginalB26NodupNumericComparisonFamily434 sourceOriginalNumericSeenFamilyLift434
    dsimp only
    by_cases hs : gate s S
    · simp only [if_pos hs]
      unfold sourceOriginalB26NumericPermutedClean434
      dsimp only [gate] at hs
      simp only [if_pos hs]
      apply Finset.sum_congr rfl
      intro nu hnu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [row,value,sign,birth,mu,valid]
      split_ifs <;> simp [sourceOriginalB26CanonicalComparisonValue434,
        sourceOriginalB26CanonicalSharedDivisor434,
        sourceOriginalB26EndpointPermutationEquiv434,mul_assoc]
    · unfold sourceOriginalB26NumericPermutedClean434
      dsimp only [gate] at hs
      simp [gate,hs]
  rw [he]
  apply target_filter_family_energy
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val)) family w hw
    birth hb gate row valid delta hdelta
  intro S hS U V ET hET hcap
  have hh := hPair U V ET hET hcap
  have hp :
      (∑ nu ∈ family,∑ s : A,(w s:ℂ)*star (U s)*(∑ t : A,row S nu s t*V nu t)) =
      ∑ nu ∈ family,sign nu *
        sourceOriginalB26TiltedPermutedFullPairing434 data q N J ell m hmJ Q hA hB
          xi zeta c theta orientation k sigma tau (fun _ => U) V nu := by
    unfold sourceOriginalB26TiltedPermutedFullPairing434
    dsimp only [row,w,value,mu,sourceOriginalBigRefreshMass434]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro nu hnu
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hp]
  exact hh

end Family

section Family
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
variable (data : SourceComparisonData434 ι G cfg x L Y Hprime)
variable [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
variable (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
variable (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
variable (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
variable (c : SourceOriginalProbePattern434 G m → ℕ)
variable (theta : SourceOriginalProbePattern434 G m → ℝ)
variable (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
variable (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
variable (epsSrc epsTgt : Bool)
local notation "BP" => fun g : G => {p : ℕ // p ∈ data.Tb g}
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Nu" => SourceOriginalProbePattern434 G m

/-- The literal auxiliary/ACTIVE ban correction with numerical inventory,
actual birth-list Nodup and pattern-dependent fresh target histories. -/
def sourceOriginalB26NodupNumericAuxBanFamily434
    (f : A → Finset ℕ → ℂ) (s : A) (S : Finset ℕ) : ℂ :=
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S then
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ t : A,
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) *
        (let birth := (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
            (fun p : Sigma BP => p.2.val)
         if Disjoint S birth then
          sourceOriginalB26CanonicalAuxBanError434 data.Tb data.Vbig J ell m hmJ nu Q
            (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu)
            zeta (theta nu) (orientation nu) k *
            (if sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val)
              J ell m hmJ nu (tau nu) t then f t (S∪birth) else 0)
         else 0)
  else 0

/-- The genuine tilted auxiliary-ban pairing lifts to numerical seen.
The arithmetic premise is discharged by the next module. There is no
history-count cost and no bound on the modulus of the future. -/
theorem source_original_B26_NODUP_NUMERIC_AUX_BAN_family_energy434
    (hmu : ∀ g (p : BP g),0 ≤ physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig g p)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hPair : ∀ (U : A → ℂ) (V : Nu → A → ℂ) (ET : ℝ), 0 ≤ ET →
      (∀ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26ActiveEnergy434 BP J ell
          (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) (V nu) ≤ ET) →
      ‖∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
        sourceOriginalB26TiltedPermutedAuxBanPairing434 data q N J ell m hmJ Q hA hB
          xi zeta c theta orientation k sigma tau (fun _ => U) V nu‖^2 ≤
      delta * sourceOriginalB26ActiveEnergy434 BP J ell
        (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) U * ET)
    (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell
      (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig)
      (sourceOriginalB26NodupNumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
        hA hB xi zeta c theta orientation k sigma tau epsSrc epsTgt f) ≤
    (delta*((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ)) *
      sourceOriginalB26NumericActiveEnergy434 BP (fun _ p => p.val) J ell
        (physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig) f := by
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let w := sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu
  let sign := fun nu : Nu =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt
  let value := fun nu : Nu => fun s t : A =>
    sourceOriginalB26CanonicalAuxBanError434 data.Tb data.Vbig J ell m hmJ nu Q
      (hA nu) (hB nu) xi (c nu) s t (sigma nu) (tau nu) zeta (theta nu) (orientation nu) k
  let birth := fun nu : Nu => fun t : A =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) (tau nu) t)).image
      (fun p : Sigma BP => p.2.val)
  let gate := fun s : A => fun S : Finset ℕ =>
    (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => p.2.val) ⊆ S
  let valid := fun nu : Nu => fun t : A =>
    sourceOriginalB26NumericBirthNodup434 BP (fun _ p => p.val) J ell m hmJ nu (tau nu) t
  let row := fun _S : Finset ℕ => fun nu : Nu => fun s t : A =>
    sign nu * sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t (sigma nu) (tau nu) * value nu s t
  have hb (nu : Nu) (_ : nu ∈ family) (t : A) :
      birth nu t ⊆ sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val) := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨a.1,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨a.2,Finset.mem_univ _,rfl⟩⟩
  have hw (s : A) : 0 ≤ w s :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (s g i)))
  have he :
      sourceOriginalB26NodupNumericAuxBanFamily434 data q N blockA blockB J ell m hmJ Q
        hA hB xi zeta c theta orientation k sigma tau epsSrc epsTgt f =
      sourceOriginalNumericSeenFamilyLift434 family birth gate
        (fun S nu s t => if valid nu t then row S nu s t else 0) f := by
    funext s S
    unfold sourceOriginalB26NodupNumericAuxBanFamily434 sourceOriginalNumericSeenFamilyLift434
    dsimp only
    by_cases hs : gate s S
    · dsimp only [gate] at hs
      simp only [gate,if_pos hs,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro nu hnu
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [row,value,sign,birth,mu,valid]
      split_ifs <;> simp [mul_assoc]
    · dsimp only [gate] at hs
      simp only [gate,if_neg hs]
  rw [he]
  apply target_filter_family_energy
    (sourceOriginalMemoryBirthPool434 BP (fun _ p => p.val)) family w hw
    birth hb gate row valid delta hdelta
  intro S hS U V ET hET hcap
  have hh := hPair U V ET hET hcap
  have hp :
      (∑ nu ∈ family,∑ s : A,(w s:ℂ)*star (U s)*(∑ t : A,row S nu s t*V nu t)) =
      ∑ nu ∈ family,sign nu *
        sourceOriginalB26TiltedPermutedAuxBanPairing434 data q N J ell m hmJ Q hA hB
          xi zeta c theta orientation k sigma tau (fun _ => U) V nu := by
    unfold sourceOriginalB26TiltedPermutedAuxBanPairing434
    dsimp only [row,w,value,mu,sourceOriginalBigRefreshMass434]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro nu hnu
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hp]
  exact hh

end Family

end Green64Analytic.CorrelationSquare

end

end

