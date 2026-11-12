module

public import Green64.Library.Weights.Part041
public import Mathlib

@[expose] public section

/-!
# Weights / SourcePeeledLiteralFourfactorTerm

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePeeledLiteralFourfactorTerm -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

/-- Actual prime-factor roughness implies absence of individual
group-prime divisibility, with the original multiplicities. -/
private theorem rough_prime_not_dvd
    (G : Finset ℕ) (m v : ℕ)
    (hm : m ≠ 0)
    (hNo : ∀ p ∈ m.primeFactors, p ∉ G)
    (hv : v ∈ G) (hPrime : v.Prime) :
    ¬v ∣ m := by
  intro hvDiv
  have hvIn : v ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hPrime, hvDiv, hm⟩
  exact hNo v hvIn hv

/-- If neither rough core factor has a marked group prime, their
product is rough as required to strip both simultaneously. -/
private theorem rough_product_not_dvd
    (G : Finset ℕ) (m p v : ℕ)
    (hm : m ≠ 0) (hp : p ≠ 0)
    (hmNo : ∀ x ∈ m.primeFactors, x ∉ G)
    (hpNo : ∀ x ∈ p.primeFactors, x ∉ G)
    (hv : v ∈ G) (hPrime : v.Prime) :
    ¬v ∣ m*p := by
  intro hvDiv
  rcases (hPrime.dvd_mul).mp hvDiv with hvm | hvp
  · exact rough_prime_not_dvd G m v hm hmNo hv hPrime hvm
  · exact rough_prime_not_dvd G p v hp hpNo hv hPrime hvp

/-- A concrete chosen small prime has only marked prime factors. -/
private theorem selected_prime_support_in_groups
    (G : Finset ℕ) (ps : ℕ) (hps : ps.Prime) (hpsG : ps ∈ G) :
    ps.primeFactors ⊆ G := by
  intro v hv
  obtain ⟨hvPrime, hvDvd, _⟩ := Nat.mem_primeFactors.mp hv
  have hEq : v = ps := (Nat.prime_dvd_prime_iff_eq hvPrime hps).mp hvDvd
  simpa [hEq] using hpsG

/-- The exact source coefficient c(n_*/(m*p)), all marked weights,
valuation parity and the designated 1/V_s factor match a fourfold
term with residual c(r'_*)W(r')ε(r'). This is a complex identity;
rational character/gcd extraction and the summation reindexing
are NOT asserted here. -/
theorem source_peeled_literal_fourfactor_term_exact
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S : Finset ℕ) (Ts : ι → Finset ℕ)
    (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (q : ℕ) (α c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (m ps p r : ℕ)
    (hm : m ≠ 0) (hps : ps.Prime) (hp : p ≠ 0) (hr : r ≠ 0)
    (hpsS : ps ∈ S) (hSG : S ⊆ G)
    (hTsG : ∀ g, Ts g ⊆ G)
    (hTbG : ∀ g, Tb g ⊆ G)
    (hParityG : Parity ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (hmNo : ∀ v ∈ m.primeFactors, v ∉ G)
    (hpNo : ∀ v ∈ p.primeFactors, v ∉ G) :
    literalSourceParity Parity (m*ps*p*r) *
      ((α m * χ m * sourceUnitTwist m σ₀ * sourceUnitTwist p σ₁ *
          c (sourceOutsidePart G (m*ps*p*r)/(m*p))) *
        (((1/Vs:ℝ):ℂ) *
          literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
            ts tb b k ((m*ps*p*r)/ps))) =
    (α m * χ m * sourceUnitTwist m σ₀ * sourceUnitTwist p σ₁) *
      (((1/Vs:ℝ):ℂ) * literalSourceParity Parity ps) *
      (c (sourceOutsidePart G r) *
        literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
          ts tb b k r * literalSourceParity Parity r) := by
  have hpsNonzero : ps ≠ 0 := hps.ne_zero
  have hpsG : ps ∈ G := hSG hpsS
  have hpsAll := selected_prime_support_in_groups G ps hps hpsG
  have hCore := source_outside_part_fourfactor_div_exact
    G m ps p r hm hpsNonzero hp hr hmNo hpNo hpsAll
  have hDiv : (m*ps*p*r)/ps = (m*p)*r := by
    calc
      _ = (ps*(m*p*r))/ps := by congr 1; ring
      _ = m*p*r := Nat.mul_div_cancel_left _ hps.pos
      _ = (m*p)*r := by ring
  have hSRough (v : ℕ) (hv : v ∈ S) :
      ¬v ∣ m*p :=
    rough_product_not_dvd G m p v hm hp hmNo hpNo
      (hSG hv) (hSPrime v hv)
  have hTsRough (g : ι) (v : ℕ) (hv : v ∈ Ts g) :
      ¬v ∣ m*p :=
    rough_product_not_dvd G m p v hm hp hmNo hpNo
      (hTsG g hv) (hTsPrime g v hv)
  have hTbRough (g : β) (v : ℕ) (hv : v ∈ Tb g) :
      ¬v ∣ m*p :=
    rough_product_not_dvd G m p v hm hp hmNo hpNo
      (hTbG g hv) (hTbPrime g v hv)
  have hWeight :
      literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k ((m*ps*p*r)/ps) =
      literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b k r := by
    rw [hDiv]
    exact literal_source_weight_mul_rough
      S Ts Tb q0 Vs Vsmall Vbig ts tb b k (m*p) r
      hSPrime hTsPrime hTbPrime hSRough hTsRough hTbRough
  have hMParity (v : ℕ) (hv : v ∈ Parity) :
      m.factorization v = 0 := by
    by_cases hvPrime : v.Prime
    · exact Nat.factorization_eq_zero_of_not_dvd
        (rough_prime_not_dvd G m v hm hmNo (hParityG hv) hvPrime)
    · exact Nat.factorization_eq_zero_of_not_prime m hvPrime
  have hPParity (v : ℕ) (hv : v ∈ Parity) :
      p.factorization v = 0 := by
    by_cases hvPrime : v.Prime
    · exact Nat.factorization_eq_zero_of_not_dvd
        (rough_prime_not_dvd G p v hp hpNo (hParityG hv) hvPrime)
    · exact Nat.factorization_eq_zero_of_not_prime p hvPrime
  have hParity := literal_source_fourfactor_parity_exact
    Parity m ps p r hm hpsNonzero hp hr hMParity hPParity
  rw [hCore, hWeight, hParity]
  ring
end Green64Analytic.CorrelationSquare

end

