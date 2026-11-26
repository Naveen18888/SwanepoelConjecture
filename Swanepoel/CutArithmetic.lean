module
public import Swanepoel.Arithmetic
@[expose] public section

namespace Swanepoel

theorem cut_not_both_small (K s z kL kR dL dR : ℤ)
    (hK : 0 ≤ K) (hz : 0 ≤ z) (hhigh : 61*K < 100*s)
    (hk : kL+kR=K+z) (hd : dL+dR=s+z)
    (hL : 100*dL < 39*kL) (hR : 100*dR < 39*kR) : False := by
  omega

theorem cut_enough_nonanchors (K s z kL kR dL dR oL : ℤ)
    (_hK : 0 ≤ K) (hz : 0 ≤ z) (hzL : z ≤ dL)
    (hhigh : 61*K < 100*s) (hk : kL+kR=K+z) (hd : dL+dR=s+z)
    (ho : dL+oL=s) (hL : 100*dL < 39*kL) (hR : 10*dR ≤ 9*kR) :
    kL-2*dL ≤ oL := by
  omega

theorem cut_product_identity (K s z kL kR dL dR oL oR : ℤ)
    (hk : kL+kR=K+z) (hd : dL+dR=s+z) (hoL : dL+oL=s) (hoR : dR+oR=s) :
    (dL+oL)*(kL-dL)+(dR+oR)*(kR-dR)=s*(K-s) := by
  rw [hoL,hoR]
  calc
    s*(kL-dL)+s*(kR-dR)=s*((kL+kR)-(dL+dR)) := by ring
    _=s*(K-s) := by rw [hk,hd]; ring

theorem N_twice (b : ℤ) : N (2*b)=b^2 := by
  unfold N
  have h : (2*b)^2=4*(b^2) := by ring
  rw [h]
  omega

theorem cut_recursive_cap (k d b o a R chosen others : ℤ)
    (hb : b=k-d) (ha : a=k-2*d)
    (hchosen : R+chosen ≤ N (k+a)) (hothers : others ≤ (o-a)*b) :
    R+chosen+others ≤ (d+o)*b := by
  have hx : k+a=2*b := by omega
  rw [hx,N_twice] at hchosen
  simp only [hb,ha] at hchosen hothers ⊢
  nlinarith

theorem disjoint_bound_from_cut (K a s R total : ℤ)
    (hR : R ≤ s*(K-s)) (htotal : total ≤ a*s) :
    R+total ≤ N (K+a) := by
  have he := N_complete_square K a s
  have hn := N_nonneg (K+a-2*s)
  nlinarith

end Swanepoel
