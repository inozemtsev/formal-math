module

public import Green64.Library.Weights.SourcePeeledLiteralFourfactorTerm
public import Green64.Library.Weights.Part039
public import Mathlib

@[expose] public section

/-!
# Weights / SourcePeeledFullSumReindex

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePeeledFullSumReindex -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/- The actual source outside part has no prime from a marked group.
This is proved from its prime-power product, not postulated. -/
theorem source_group_prime_not_dvd_outside
    (G : Finset ℕ) (n v : ℕ) (hvPrime : v.Prime) (hvG : v ∈ G) :
    ¬v ∣ sourceOutsidePart G n := by
  classical
  unfold sourceOutsidePart
  apply Prime.not_dvd_finsetProd (Nat.prime_iff.mp hvPrime)
  intro p hp
  have hpOut : p ∉ G := (Finset.mem_filter.mp hp).2
  have hpPrime : p.Prime := (Nat.mem_primeFactors.mp
    (Finset.mem_filter.mp hp).1).1
  intro hvPow
  have hvDiv : v ∣ p := hvPrime.dvd_of_dvd_pow hvPow
  have hvEq : v = p := (Nat.prime_dvd_prime_iff_eq hvPrime hpPrime).mp hvDiv
  exact hpOut (hvEq ▸ hvG)

/- Every divisor of the actual source outside part is rough. -/
theorem source_divisor_of_outside_rough
    (G : Finset ℕ) (n m : ℕ)
    (hm : m ∣ sourceOutsidePart G n) :
    ∀ v ∈ m.primeFactors, v ∉ G := by
  intro v hv hvG
  have ⟨hvPrime, hvDiv, _⟩ := Nat.mem_primeFactors.mp hv
  exact source_group_prime_not_dvd_outside G n v hvPrime hvG (hvDiv.trans hm)
/- Every marked prime dividing a positive source integer divides
the complementary inside part, with the original multiplicity. -/
theorem source_group_prime_dvd_inside
    (G : Finset ℕ) (n ps : ℕ) (hn : n ≠ 0)
    (hPrime : ps.Prime) (hpsG : ps ∈ G) (hpsDiv : ps ∣ n) :
    ps ∣ sourceInsidePart G n := by
  classical
  have hpMem : ps ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hPrime, hpsDiv, hn⟩
  have hpPow : ps ^ 1 ∣ n := by simpa using hpsDiv
  have hpExp : 1 ≤ n.factorization ps :=
    (hPrime.pow_dvd_iff_le_factorization hn).mp hpPow
  unfold sourceInsidePart
  have hpProd : ps ^ 1 ∣
      ∏ p ∈ n.primeFactors with p ∈ G, p ^ n.factorization p :=
    (Nat.pow_dvd_pow ps hpExp).trans
      (Finset.dvd_prod_of_mem (fun p => p ^ n.factorization p)
        (Finset.mem_filter.mpr ⟨hpMem, hpsG⟩))
  simpa using hpProd

/- Source extraction and core divisibility construct the unique
positive r' with n = m p_s p r'. -/
theorem source_actual_fourfactor_quotient
    (G S : Finset ℕ) (n m ps p : ℕ)
    (hn : 0 < n) (hSG : S ⊆ G)
    (hpsPrime : ∀ v ∈ S, v.Prime)
    (hps : ps ∈ smallPrimeSupport S n)
    (hMP : m*p ∣ sourceOutsidePart G n) :
    n = (m*ps*p) * (n/(m*ps*p)) := by
  have hpsS : ps ∈ S := (Finset.mem_filter.mp hps).1
  have hpsDvd : ps ∣ n := (Finset.mem_filter.mp hps).2
  have hpPos : 0 < ps := (hpsPrime ps hpsS).pos
  have hInside : ps ∣ sourceInsidePart G n :=
    source_group_prime_dvd_inside G n ps (Nat.ne_of_gt hn)
      (hpsPrime ps hpsS) (hSG hpsS) hpsDvd
  have hMPcopy := hMP
  obtain ⟨a,ha⟩ := hMP
  obtain ⟨b,hb⟩ := hInside
  have hpFactor : 0 < m*p := by
    have hStar : sourceOutsidePart G n ≠ 0 := by
      intro hzero
      have := sourceParts_mul G n (Nat.ne_of_gt hn)
      rw [hzero] at this
      simp at this
      omega
    have hpDvd : m*p ∣ sourceOutsidePart G n := hMPcopy
    exact Nat.pos_of_dvd_of_pos hpDvd (Nat.pos_of_ne_zero hStar)
  have hFactor : 0 < m*ps*p := by
    nlinarith [hpFactor, hpPos]
  have hEquation : n = (m*ps*p)*(a*b) := by
    calc
      n = sourceOutsidePart G n * sourceInsidePart G n :=
        (sourceParts_mul G n (Nat.ne_of_gt hn)).symm
      _ = (m*p*a)*(ps*b) := by rw [ha,hb]
      _ = (m*ps*p)*(a*b) := by ring
  rw [hEquation]
  simp only [Nat.mul_div_cancel_left _ hFactor]

/- The source is indexed by an ordered pair (m,p) and a *chosen*
small prime p_s. Different choices of p_s remain different indices. -/
noncomputable def sourcePeeledTripleIndices
    (G S primeSlot : Finset ℕ) (n : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  let D := (sourceOutsidePart G n).divisors
  ((D.product D).product (smallPrimeSupport S n)).filter
    (fun z => z.1.2 ∈ primeSlot ∧ z.1.2.Prime ∧
      z.1.1*z.1.2 ∣ sourceOutsidePart G n)

def sourcePeeledQuadEncode (n : ℕ) :
    ((ℕ × ℕ) × ℕ) → ((ℕ × ℕ) × (ℕ × ℕ)) :=
  fun z => ((z.1.1,z.2),
    (z.1.2,n/(z.1.1*z.2*z.1.2)))

/- The genuine four-factor index set is the *image* of the precise
source indices, so it tracks all slot and mark multiplicities. -/
noncomputable def sourcePeeledQuadIndices
    (G S primeSlot : Finset ℕ) (n : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (sourcePeeledTripleIndices G S primeSlot n).image
    (sourcePeeledQuadEncode n)

/- No collision: the fourfold index retains all three original
choices, hence does not quotient away multiplicities. -/
theorem source_peeled_quad_encode_injective (n : ℕ) :
    Function.Injective (sourcePeeledQuadEncode n) := by
  intro x y hxy
  rcases x with ⟨⟨m,p⟩,ps⟩
  rcases y with ⟨⟨m',p'⟩,ps'⟩
  simp only [sourcePeeledQuadEncode, Prod.mk.injEq] at hxy
  rcases hxy with ⟨⟨hm,hps⟩, ⟨hp,_⟩⟩
  subst m'
  subst p'
  subst ps'
  rfl

/- A full finite-sum reindex with the injective map; this is an
honest sum over ordered fourfold representations, not an L² identity. -/
theorem source_peeled_quad_sum_reindex
    (G S primeSlot : Finset ℕ) (n : ℕ)
    (f : ((ℕ × ℕ) × (ℕ × ℕ)) → ℂ) :
    (∑ z ∈ sourcePeeledQuadIndices G S primeSlot n, f z) =
      ∑ z ∈ sourcePeeledTripleIndices G S primeSlot n,
        f (sourcePeeledQuadEncode n z) := by
  classical
  unfold sourcePeeledQuadIndices
  exact Finset.sum_image
    (fun x hx y hy hxy =>
      source_peeled_quad_encode_injective n hxy)

/- Every index has the actual product n and the actual source
divisor/slot/mark restrictions. No quotient is rounded. -/
theorem source_peeled_quad_product_exact
    (G S primeSlot : Finset ℕ) (n : ℕ)
    (hn : 0 < n) (hSG : S ⊆ G)
    (hPrime : ∀ v ∈ S, v.Prime)
    (z : ((ℕ × ℕ) × (ℕ × ℕ)))
    (hz : z ∈ sourcePeeledQuadIndices G S primeSlot n) :
    z.1.1 * z.1.2 * z.2.1 * z.2.2 = n := by
  classical
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
  have htPair := (Finset.mem_filter.mp ht).1
  have htS := (Finset.mem_product.mp htPair).2
  have htC := (Finset.mem_filter.mp ht).2
  have hDiv : t.1.1*t.1.2 ∣ sourceOutsidePart G n := htC.2.2
  have hFactor :=
    source_actual_fourfactor_quotient G S n t.1.1 t.2 t.1.2
      hn hSG hPrime htS hDiv
  simpa only [sourcePeeledQuadEncode] using hFactor.symm

/- Finite distributivity for the complete source indices. -/
private theorem source_complete_triple_distributivity
    (D T : Finset ℕ) (eligible : ℕ → ℕ → Prop)
    [DecidableRel eligible] (u : ℕ → ℕ → ℂ) (v : ℕ → ℂ) (eps scale : ℂ) :
    eps * ((∑ m ∈ D, ∑ p ∈ D,
               if eligible m p then u m p else 0) *
             (scale * ∑ ps ∈ T, v ps)) =
      ∑ z ∈ ((D.product D).product T).filter
          (fun z => eligible z.1.1 z.1.2),
        eps * (u z.1.1 z.1.2 * (scale * v z.2)) := by
  classical
  calc
    _ = eps * ((∑ mp ∈ D.product D,
            if eligible mp.1 mp.2 then u mp.1 mp.2 else 0) *
          (∑ ps ∈ T, scale * v ps)) := by
          rw [← Finset.sum_product', Finset.mul_sum]
          rfl
    _ = eps * (∑ z ∈ (D.product D).product T,
          (if eligible z.1.1 z.1.2 then u z.1.1 z.1.2 else 0) *
            (scale * v z.2)) := by
          rw [Finset.sum_mul_sum, ← Finset.sum_product']
          rfl
    _ = ∑ z ∈ (D.product D).product T,
          eps * ((if eligible z.1.1 z.1.2 then u z.1.1 z.1.2 else 0) *
            (scale * v z.2)) := by
          rw [Finset.mul_sum]
    _ = _ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro z hz
          split_ifs <;> ring

/- The source residual BEFORE rational-center character expansion.
In particular it does not contain any gcd or new character filter. -/
noncomputable def sourceRawMarkedResidual
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ) (r : ℕ) : ℂ :=
  c (sourceOutsidePart G r) *
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k r *
    literalSourceParity Parity r

/- Reindex an actual source term; the rough-core assumptions of the
earlier individual-term theorem are DERIVED from divisor membership. -/
theorem source_triple_term_to_raw_residual
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k q : ℕ)
    (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ) (n m p ps : ℕ)
    (hn : 0 < n)
    (hSG : S ⊆ G) (hParityG : Parity ⊆ G)
    (hTsG : ∀ g, Ts g ⊆ G)
    (hTbG : ∀ g, Tb g ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (hz : ((m,p),ps) ∈ sourcePeeledTripleIndices G S primeSlot n) :
    literalSourceParity Parity n *
      ((α m * χ m * sourceUnitTwist m σ₀ *
          sourceUnitTwist p σ₁ *
          c (sourceOutsidePart G n/(m*p))) *
       (((1/Vs:ℝ):ℂ) *
         literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
           ts tb b k (n/ps))) =
    (α m * χ m * sourceUnitTwist m σ₀ * sourceUnitTwist p σ₁) *
      (((1/Vs:ℝ):ℂ) * literalSourceParity Parity ps) *
      sourceRawMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k G Parity c (n/(m*ps*p)) := by
  classical
  have hpairs := (Finset.mem_filter.mp hz).1
  have hpmem := (Finset.mem_product.mp hpairs).1
  have hps := (Finset.mem_product.mp hpairs).2
  have hmMem := (Finset.mem_product.mp hpmem).1
  have hpMem := (Finset.mem_product.mp hpmem).2
  have hMP : m*p ∣ sourceOutsidePart G n :=
    (Finset.mem_filter.mp hz).2.2.2
  have hmDiv := (Nat.mem_divisors.mp hmMem).1
  have hpDiv := (Nat.mem_divisors.mp hpMem).1
  have hStar : sourceOutsidePart G n ≠ 0 :=
    (Nat.mem_divisors.mp hmMem).2
  have hm : m ≠ 0 :=
    Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hmDiv (Nat.pos_of_ne_zero hStar))
  have hp : p ≠ 0 :=
    Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hpDiv (Nat.pos_of_ne_zero hStar))
  have hpsS : ps ∈ S := (Finset.mem_filter.mp hps).1
  have hpsPrime : ps.Prime := hSPrime ps hpsS
  have hN := source_actual_fourfactor_quotient G S n m ps p
    hn hSG hSPrime hps hMP
  have hr : n/(m*ps*p) ≠ 0 := by
    intro hr0
    rw [hr0] at hN
    simp at hN
    omega
  have hmRough := source_divisor_of_outside_rough G n m hmDiv
  have hpRough := source_divisor_of_outside_rough G n p hpDiv
  have hTerm := source_peeled_literal_fourfactor_term_exact
    G Parity S Ts Tb q0 Vs Vsmall Vbig ts tb b k q α c χ σ₀ σ₁
    m ps p (n/(m*ps*p))
    hm hpsPrime hp hr hpsS hSG hTsG hTbG hParityG
    hSPrime hTsPrime hTbPrime hmRough hpRough
  unfold sourceRawMarkedResidual
  simpa only [← hN] using hTerm

/- The COMPLETE n-th source coefficient is a sum over distinct
four-factor representations. This is an equality in ℂ. -/
theorem source_peeled_full_sum_to_raw_residual
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k q : ℕ)
    (α c : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ) (n : ℕ)
    (hn : 0 < n)
    (hSG : S ⊆ G) (hParityG : Parity ⊆ G)
    (hTsG : ∀ g, Ts g ⊆ G)
    (hTbG : ∀ g, Tb g ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime) :
    literalSourceParity Parity n *
      ((∑ m ∈ (sourceOutsidePart G n).divisors,
        ∑ p ∈ (sourceOutsidePart G n).divisors,
          if p ∈ primeSlot ∧ p.Prime ∧
               m*p ∣ sourceOutsidePart G n then
            α m * χ m * sourceUnitTwist m σ₀ *
              sourceUnitTwist p σ₁ *
              c (sourceOutsidePart G n/(m*p))
          else 0) *
       (((1/Vs:ℝ):ℂ) *
        ∑ ps ∈ smallPrimeSupport S n,
          literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
            ts tb b k (n/ps))) =
      ∑ z ∈ sourcePeeledQuadIndices G S primeSlot n,
        (α z.1.1 * χ z.1.1 * sourceUnitTwist z.1.1 σ₀ *
           sourceUnitTwist z.2.1 σ₁) *
        (((1/Vs:ℝ):ℂ) * literalSourceParity Parity z.1.2) *
        sourceRawMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
          ts tb b k G Parity c z.2.2 := by
  classical
  let D : Finset ℕ := (sourceOutsidePart G n).divisors
  let T : Finset ℕ := smallPrimeSupport S n
  let eligible : ℕ → ℕ → Prop := fun m p =>
    p ∈ primeSlot ∧ p.Prime ∧ m*p ∣ sourceOutsidePart G n
  let u : ℕ → ℕ → ℂ := fun m p =>
    α m * χ m * sourceUnitTwist m σ₀ *
      sourceUnitTwist p σ₁ * c (sourceOutsidePart G n/(m*p))
  let v : ℕ → ℂ := fun ps =>
    literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k (n/ps)
  let eps : ℂ := literalSourceParity Parity n
  let scale : ℂ := ((1/Vs:ℝ):ℂ)
  let f : ((ℕ×ℕ)×(ℕ×ℕ)) → ℂ := fun z =>
    (α z.1.1 * χ z.1.1 * sourceUnitTwist z.1.1 σ₀ *
      sourceUnitTwist z.2.1 σ₁) *
      (scale * literalSourceParity Parity z.1.2) *
      sourceRawMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k G Parity c z.2.2
  have hExpand := source_complete_triple_distributivity
      D T eligible u v eps scale
  calc
    _ = ∑ z ∈ sourcePeeledTripleIndices G S primeSlot n,
          eps * (u z.1.1 z.1.2 * (scale * v z.2)) := by
          simpa only [D,T,eligible,u,v,eps,scale,
            sourcePeeledTripleIndices] using hExpand
    _ = ∑ z ∈ sourcePeeledTripleIndices G S primeSlot n,
          f (sourcePeeledQuadEncode n z) := by
          apply Finset.sum_congr rfl
          intro z hz
          rcases z with ⟨⟨m,p⟩,ps⟩
          have hTerm := source_triple_term_to_raw_residual
            G Parity S primeSlot Ts Tb
            q0 Vs Vsmall Vbig ts tb b k q
            α c χ σ₀ σ₁ n m p ps
            hn hSG hParityG hTsG hTbG hSPrime hTsPrime hTbPrime hz
          simpa only [eps,u,v,scale,f,sourcePeeledQuadEncode] using hTerm
    _ = _ := by
          symm
          exact source_peeled_quad_sum_reindex G S primeSlot n f

/-- Exact original Fourier extraction into the complete ordered four-factor
sum, before any rational-center decomposition. -/
theorem source_peeled_original_fourier_full_reindex
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N q : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
       ((Finset.univ : Finset β).biUnion Tb))
    (hParityG : Ptwist ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (n : ℕ) :
    fourierCoeff (T := 1)
      (sourcePeeledMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig
         ts tb b k primeSlot Ptwist α c χ σ₀ σ₁) (n:ℤ) =

      if n ∈ Finset.Icc 1 N then
        ∑ z ∈ sourcePeeledQuadIndices G S primeSlot n,
          (α z.1.1 * χ z.1.1 * sourceUnitTwist z.1.1 σ₀ *
             sourceUnitTwist z.2.1 σ₁) *
          (((1/Vs:ℝ):ℂ) * literalSourceParity Ptwist z.1.2) *
          sourceRawMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb b k G Ptwist c z.2.2
      else 0 := by
  classical
  rw [source_peeled_fourier_triple_coefficient_exact]
  by_cases hI : n ∈ Finset.Icc 1 N
  · simp only [hI, ite_true]
    have hn : 0 < n := (Finset.mem_Icc.mp hI).1
    have hSG : S ⊆ G := by
      intro v hv
      rw [hG]
      simp [hv]
    have hTsG : ∀ g, Ts g ⊆ G := by
      intro g v hv
      rw [hG]
      simp only [Finset.mem_union, Finset.mem_biUnion]
      exact Or.inl (Or.inr ⟨g, Finset.mem_univ _, hv⟩)
    have hTbG : ∀ g, Tb g ⊆ G := by
      intro g v hv
      rw [hG]
      simp only [Finset.mem_union, Finset.mem_biUnion]
      exact Or.inr ⟨g, Finset.mem_univ _, hv⟩
    have hSum := source_peeled_full_sum_to_raw_residual
      G Ptwist S primeSlot Ts Tb q0 Vs Vsmall Vbig
      ts tb b k q α c χ σ₀ σ₁ n
      hn hSG hParityG hTsG hTbG hSPrime hTsPrime hTbPrime
    simpa only [← hG] using hSum
  · simp only [hI, ite_false]
end Green64Analytic.CorrelationSquare

end

