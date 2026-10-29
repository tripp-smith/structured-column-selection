"""Squared spectral check for columns {0, 2} of the rational 2×3 frame.

The small right singular direction is (0, 1). Its image energy is 16/25,
and 1 + k(n - k) = 3. This does not call CPQR and is not the theorem.
"""

from fractions import Fraction as F


def test_columns_02_meet_the_spectral_factor():
    columns = [[F(1), F(0)], [F(0), F(4, 5)]]
    x = [F(0), F(1)]
    image = [
        columns[0][0] * x[0] + columns[0][1] * x[1],
        columns[1][0] * x[0] + columns[1][1] * x[1],
    ]
    energy_x = x[0] ** 2 + x[1] ** 2
    energy_image = image[0] ** 2 + image[1] ** 2
    factor = 1 + F(2) * (F(3) - F(2))
    assert energy_image == F(16, 25)
    assert factor == 3
    assert energy_x <= factor * energy_image
