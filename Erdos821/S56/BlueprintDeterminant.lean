import Erdos821.Blueprint.TypeII
import Erdos821.S56.Determinant
import Erdos821.S56.DeterminantConverse

namespace Erdos821.Blueprint

theorem determinant_forward (m m' n e h h' k : ℤ)
    (hm : m * n = 2 * e * h + 1) (hm' : m' * n = 2 * e * h' + 1)
    (he : e ≠ 0) (hk : m' - m = 2 * e * k) :
    h' - h = k * n ∧ m * h' - m' * h = k :=
  Erdos821.S56.determinant_forward_of_increment m m' n e h h' k hm hm' he hk


theorem determinant_converse (m m' e h h' k : ℤ)
    (hm : 0 < m) (he : 0 < e) (hh : 0 < h)
    (hdelta : m' - m = 2 * e * k) (hcross : m * h' - m' * h = k)
    (hcop : IsCoprime m k) :
    ∃ n : ℤ, 0 < n ∧ m * n = 2 * e * h + 1 ∧ m' * n = 2 * e * h' + 1 :=
  (Erdos821.S56.determinant_converse_unique m m' e h h' k
    hm he hh hdelta hcross hcop).exists



end Erdos821.Blueprint
