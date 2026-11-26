module
public import Swanepoel.Quantitative
@[expose] public section

noncomputable section
namespace Swanepoel

def bankRawU (ell k y h : ℝ) : ℝ :=
  9*ell^2/8+ell*(k+h)/2+(411/2500:ℝ)*(11*ell/6+2*k-h-2*y/3)^2

theorem bankU_le_at_lower_H (rho x L H : ℝ) (hrho : 0≤rho) (hx : 0≤x)
    (hLH : L≤H) (hH : H≤2-9*x/5) : bankU rho x H≤bankU rho x L := by
  have hdelta : 0≤H-L := sub_nonneg.mpr hLH
  have hreturn : 0≤2-H-2*x/3 := by linarith only [hH,hx]
  have hfactor : 0≤(411/2500:ℝ)*(H-L)+(411/1250:ℝ)*(2-H-2*x/3)+(257/2500:ℝ)*rho := by
    positivity
  have heq : bankU rho x L-bankU rho x H=
      (H-L)*((411/2500:ℝ)*(H-L)+(411/1250:ℝ)*(2-H-2*x/3)+(257/2500:ℝ)*rho) := by
    unfold bankU
    ring
  exact sub_nonneg.mp (heq.symm ▸ mul_nonneg hdelta hfactor)

theorem bankRawU_normalization (ell k y h : ℝ) (hk : k≠0) :
    bankRawU ell k y h=k^2*bankU (ell/k) (y/k) (h/k) := by
  unfold bankRawU bankU
  field_simp

theorem bankRawU_of_weighted_counts (ell k y h R X M Z B v : ℝ)
    (hR : R=X+M+Z)
    (hX : X≤3*ell^2/2) (hM : M≤ell*(k+h))
    (hB : B=5*ell/2+2*k-h) (hv : v=ell+y)
    (harea : X/4+M/2+Z≤(411/2500:ℝ)*(B-2*v/3)^2) :
    R≤bankRawU ell k y h := by
  have hsplit : R=(X/4+M/2+Z)+3*X/4+M/2 := by rw [hR]; ring
  rw [hsplit]
  calc
    _ ≤ (411/2500:ℝ)*(B-2*v/3)^2+9*ell^2/8+ell*(k+h)/2 := by
      linarith only [harea,hX,hM]
    _ = bankRawU ell k y h := by rw [hB,hv]; unfold bankRawU; ring

theorem high_bank_bound_of_raw_estimate (ell k y h R : ℝ)
    (hell : 0≤ell) (hk : 0≤k) (hy : 0≤y) (hh : 0≤h)
    (hthree : y≤4*h-k) (hfour : 2*y≤h+k) (hfive : 9*y≤10*k-5*h)
    (hhigh : (61/100:ℝ)*(3*ell+k)≤2*ell+y)
    (hR : R≤bankRawU ell k y h) :
    R≤(2*ell+y)*((3*ell+k)-(2*ell+y)) := by
  rcases eq_or_lt_of_le hk with hk0 | hkpos
  · have hkzero : k=0 := hk0.symm
    have hyzero : y=0 := by rw [hkzero] at hfive; linarith only [hfive,hy,hh]
    have hhzero : h=0 := by rw [hkzero,hyzero] at hfive; linarith only [hfive,hh]
    rw [hkzero,hyzero,hhzero] at hR
    rw [hkzero,hyzero]
    unfold bankRawU at hR
    nlinarith only [hR,sq_nonneg ell]
  · let rho := ell/k
    let x := y/k
    let H := h/k
    have hrho : 0≤rho := div_nonneg hell hkpos.le
    have hx : 0≤x := div_nonneg hy hkpos.le
    have hrhok : rho*k=ell := div_mul_cancel₀ _ (ne_of_gt hkpos)
    have hxk : x*k=y := div_mul_cancel₀ _ (ne_of_gt hkpos)
    have hHk : H*k=h := div_mul_cancel₀ _ (ne_of_gt hkpos)
    have hxlo : (61/100:ℝ)-17*rho/100≤x := by
      apply (mul_le_mul_iff_right₀ hkpos).mp
      nlinarith only [hhigh,hrhok,hxk]
    have hHone : (1+x)/4≤H := by
      apply (mul_le_mul_iff_right₀ hkpos).mp
      nlinarith only [hthree,hxk,hHk]
    have hHtwo : 2*x-1≤H := by
      apply (mul_le_mul_iff_right₀ hkpos).mp
      nlinarith only [hfour,hxk,hHk]
    have hHupper : H≤2-9*x/5 := by
      apply (mul_le_mul_iff_right₀ hkpos).mp
      nlinarith only [hfive,hxk,hHk]
    have hxhi : x≤4/5 := by linarith only [hHtwo,hHupper]
    have hHlower : bankH0 x≤H := max_le hHone hHtwo
    have hU := bankU_le_at_lower_H rho x (bankH0 x) H hrho hx hHlower hHupper
    have hgap := bankGap_nonneg rho x hrho hxlo hxhi
    have hbound : bankU rho x (bankH0 x)≤(2*rho+x)*(1+rho-x) := by
      unfold bankGap at hgap
      linarith only [hgap]
    calc
      R ≤ bankRawU ell k y h := hR
      _ = k^2*bankU rho x H := bankRawU_normalization ell k y h (ne_of_gt hkpos)
      _ ≤ k^2*bankU rho x (bankH0 x) := mul_le_mul_of_nonneg_left hU (sq_nonneg k)
      _ ≤ k^2*((2*rho+x)*(1+rho-x)) := mul_le_mul_of_nonneg_left hbound (sq_nonneg k)
      _ = (2*ell+y)*((3*ell+k)-(2*ell+y)) := by
        dsimp [rho,x]
        field_simp
        ring

theorem lemma_3_8_of_geometric_estimates (ell k y h R : ℝ)
    (hell : 0≤ell) (hk : 0≤k) (hy : 0≤y) (hh : 0≤h)
    (hthree : y≤4*h-k) (hfour : 2*y≤h+k) (hfive : 9*y≤10*k-5*h)
    (hquadratic : R≤(2379/10000:ℝ)*(3*ell+k)^2)
    (hraw : R≤bankRawU ell k y h)
    (hlow : (39/100:ℝ)*(3*ell+k)≤2*ell+y) :
    R≤(2*ell+y)*((3*ell+k)-(2*ell+y)) := by
  by_cases hmoderate : 2*ell+y≤(61/100:ℝ)*(3*ell+k)
  · exact moderate_bank_bound R (3*ell+k) (2*ell+y) hquadratic hlow hmoderate
  · exact high_bank_bound_of_raw_estimate ell k y h R hell hk hy hh hthree hfour hfive
      (le_of_lt (lt_of_not_ge hmoderate)) hraw

end Swanepoel
