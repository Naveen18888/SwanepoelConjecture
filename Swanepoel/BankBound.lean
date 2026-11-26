module
public import Swanepoel.BankPortProjection
public import Swanepoel.HalfSystemBankRealization
@[expose] public section

noncomputable section
namespace Swanepoel

theorem bank_bound_from_projection (k b d : ℝ) (hd : 0≤d)
    (hB : 3*b≤5*k) (hcone : (1+Real.sqrt 3/2)*d≤b) :
    39*d≤35*k ∧ 10*d≤9*k := by
  have hs : (12/7:ℝ)≤Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3:ℝ),Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  have hscale := mul_nonneg (sub_nonneg.mpr hs) hd
  have hstrong : 39*d≤35*k := by nlinarith
  exact ⟨hstrong,by linarith⟩

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bank_three_boundary_le_five_K (ht : G.TriangleFree) (side : Bool) :
    3*((B.bankBoundaryPorts ht side).card : ℤ)≤5*B.bankK ht side :=
  G.partial_family_three_boundary_le_five_K ht _ (Finset.filter_subset _ _)

theorem bank_bound_strong (ht : G.TriangleFree) (side : Bool) :
    39*((B.bankMeetingAnchors ht side).card : ℤ)≤35*B.bankK ht side ∧
      10*((B.bankMeetingAnchors ht side).card : ℤ)≤9*B.bankK ht side := by
  have hB : 3*((B.bankBoundaryPorts ht side).card : ℝ)≤5*(B.bankK ht side : ℝ) := by
    exact_mod_cast B.bank_three_boundary_le_five_K ht side
  have hh := bank_bound_from_projection (B.bankK ht side : ℝ)
    ((B.bankBoundaryPorts ht side).card : ℝ) ((B.bankMeetingAnchors ht side).card : ℝ)
    (Nat.cast_nonneg _) hB (B.bank_boundary_cone_bound ht side)
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

theorem bank_bound (ht : G.TriangleFree) (side : Bool) :
    10*((B.bankMeetingAnchors ht side).card : ℤ)≤9*B.bankK ht side :=
  (B.bank_bound_strong ht side).2

end OrdinaryCutBanks

theorem HalfSystem.BankRealization.bankBound {n : ℕ} {G : PennyGraph n}
    {cut : TrackComponent G} {H : HalfSystem} {B : OrdinaryCutBanks G cut}
    {ht : G.TriangleFree} {side : Bool} (R : H.BankRealization B ht side) : H.BankBound := by
  classical
  have hp : H.tracks.p=(B.bankAnchorTracks ht side).card := by
    rw [← R.anchors,Finset.card_image_of_injective _ R.injective]
    rfl
  have hd : H.bankAnchors.card=(B.bankMeetingAnchors ht side).card := by
    rw [← R.bank,Finset.card_image_of_injective _ R.injective]
  change 10*(H.bankAnchors.card : ℤ)≤9*H.tracks.K
  rw [hd,TrackSystem.K,hp,R.defects]
  exact B.bank_bound ht side

end Swanepoel
