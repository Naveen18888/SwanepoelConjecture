module
public import Swanepoel.L38Assembly
public import Swanepoel.Tracks
public import Swanepoel.L38BankArithmetic
@[expose] public section

noncomputable section
namespace Swanepoel

theorem HalfSystem.highBankBound_of_weighted_counts (H : HalfSystem)
    (ell k y h X M Z B v : ℝ)
    (hell : 0≤ell) (hk : 0≤k) (hy : 0≤y) (hh : 0≤h)
    (hK : (H.k : ℝ)=3*ell+k) (hD : (H.d : ℝ)=2*ell+y)
    (hR : (H.R : ℝ)=X+M+Z)
    (hthree : y≤4*h-k) (hfour : 2*y≤h+k) (hfive : 9*y≤10*k-5*h)
    (hX : X≤3*ell^2/2) (hM : M≤ell*(k+h))
    (hB : B=5*ell/2+2*k-h) (hv : v=ell+y)
    (harea : X/4+M/2+Z≤(411/2500:ℝ)*(B-2*v/3)^2)
    (hquadratic : H.tracks.QuadraticBound) : H.HighBankBound := by
  have hQint : 10000*H.R≤2379*H.k^2 := hquadratic
  have hQreal : (10000:ℝ)*(H.R : ℝ)≤2379*(H.k : ℝ)^2 := by exact_mod_cast hQint
  rw [hK] at hQreal
  have hQ : (H.R : ℝ)≤(2379/10000:ℝ)*(3*ell+k)^2 := by linarith only [hQreal]
  have hraw := bankRawU_of_weighted_counts ell k y h (H.R : ℝ) X M Z B v
    hR hX hM hB hv harea
  intro hhigh
  have hhighR : (39:ℝ)*(H.k : ℝ)≤100*(H.d : ℝ) := by exact_mod_cast hhigh
  rw [hK,hD] at hhighR
  have hlo : (39/100:ℝ)*(3*ell+k)≤2*ell+y := by linarith only [hhighR]
  have hbound := lemma_3_8_of_geometric_estimates ell k y h (H.R : ℝ)
    hell hk hy hh hthree hfour hfive hQ hraw hlo
  rw [← hK,← hD] at hbound
  exact_mod_cast hbound

theorem HalfSystem.BankRealization.highBankBound_of_geometric_counts
    {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G}
    {H : HalfSystem} {B : OrdinaryCutBanks G cut} {ht : G.TriangleFree} {side : Bool}
    (R : H.BankRealization B ht side)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a) :
    let ell : ℝ := (B.isolatedTwoPortPentagons ht side).card
    let k : ℝ := G.familyK (B.bankRemainder ht side)
    let y : ℝ := (B.subfamilyMeetingPorts (B.bankRemainder ht side)).card
    let h : ℝ := G.familyPortExcess (B.bankRemainder ht side)
    ∀ X M Z : ℝ,(H.R : ℝ)=X+M+Z →
      X≤3*ell^2/2 → M≤ell*(k+h) →
      X/4+M/2+Z≤(411/2500:ℝ)*(5*ell/2+2*k-h-2*(ell+y)/3)^2 →
      H.tracks.QuadraticBound → H.HighBankBound := by
  dsimp only
  intro X M Z hR hX hM harea hquadratic
  obtain ⟨hell,hk,hy,hh,hK,hD,hthree,hfour,hfive⟩ := R.bank_arithmetic_parameters hdegree
  exact H.highBankBound_of_weighted_counts _ _ _ _ X M Z _ _
    hell hk hy hh hK hD hR hthree hfour hfive hX hM rfl rfl harea hquadratic

end Swanepoel
