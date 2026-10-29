"""Exact column-energy ratio of the wide family.

This recomputes triangular and LDL completion energies. It is not the
Lean theorem.
"""

from fractions import Fraction as F

from structselect.wide_cpqr import compressed_certificate, triangular_block


def test_explicit_column_energy_ratio_beats_eight_m_squared():
    for value in (2, 3, 4):
        block, _ = triangular_block(value)
        k = len(block)
        lead = [sum(block[i][j] ** 2 for i in range(k)) for j in range(k)]
        fill = compressed_certificate(value)["completion_column_energies"]
        ratio_num = max(lead)
        ratio_den = min(fill)
        assert ratio_den > 0
        assert ratio_num * 1 >= F(8 * value * value) * ratio_den
        assert all(isinstance(entry, F) for entry in lead + fill)
