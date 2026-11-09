# The colouring

r1212_1660.graph has 1660 lines of 1660 characters, 2,757,260 bytes. Character w of line v is 1 if the edge vw is red and 0 if it is blue. The diagonal is 0. SHA-256: see SHA256SUMS.

There is no red K₁₂ and no blue K₁₂, so R(12,12) ≥ 1661.

## M(797) and its antipodes

M(797) is the Mathon–Shearer colouring, in the vertex order of r1212-1642: A_x = x for x in Z/797 (0–796), B_x = 797 + x (797–1593), a = 1594 and b = 1595.

- A_x A_y and B_x B_y are red iff x − y is a nonzero square mod 797;
- A_x B_y is red iff x ≠ y and x − y is not a square;
- a is red to all of A, b is red to all of B, and every other pair is blue.

The **antipode** of A_x is B_x, and the antipode of a is b. Each vertex and its antipode are joined by a blue edge, and towards every other vertex they have opposite colours (this uses that −1 is a square mod 797).

## The target set Σ_V

Σ_V has 21 vertices of M(797):

- C = (c₀, …, c₉) = (930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595), a red K₁₀;
- I = (i₀, …, i₉) = (1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267), a blue K₁₀;
- ī₆ = 675 = A₆₇₅, the antipode of i₆ = 1472 = B₆₇₅. It is written i6bar in r1212_1660.json and in the outputs of the checks.

C and I are the certificates of r1212-1642 and r1212-1658. Σ_V contains exactly two antipodal pairs: {a, b} = {i₅, c₉}, which r1212-1658 already has, and the new pair {i₆, ī₆}.

These names count from 0, as in r1212-1642 and r1212-1658. The paper counts from 1: its c_p and i_p are c_{p−1} and i_{p−1} here, and its ī₇ is ī₆ here (see the table in the top-level README).

## Vertex order

| Vertices | Role |
|---|---|
| 0–1574 | V°: the 1575 vertices of M(797) outside Σ_V, in increasing order |
| 1575–1659 | T: the 85 core vertices |

The colours among the vertices of V° are those of M(797). This order differs from r1212-1658, where vertices 0–1595 were all of M(797).

## The core vertices

Each core vertex has one of three types towards V°:

- **copy of g**, for some g in Σ_V: the edge to every x in V° has the colour of gx in M(797);
- **constant red**: all edges to V° are red;
- **constant blue**: all edges to V° are blue.

The colours among the 85 core vertices are given by the file. Σ_V itself is not part of the colouring: every core vertex is described only by its type, and each vertex of Σ_V has 2, 3 or 4 copies.

| Vertices | Type |
|---|---|
| 1575 | copy of c1 = 926 |
| 1576 | copy of c0 = 930 |
| 1577 | copy of c2 = 1573 |
| 1578 | copy of i5 = 1594 |
| 1579 | copy of i9 = 1267 |
| 1580 | copy of i6 = 1472 |
| 1581 | copy of c7 = 1582 |
| 1582 | copy of c4 = 1479 |
| 1583 | copy of c5 = 1483 |
| 1584 | copy of c6 = 1492 |
| 1585 | copy of i3 = 1549 |
| 1586 | copy of i4 = 1554 |
| 1587 | copy of i7 = 1557 |
| 1588 | copy of c2 = 1573 |
| 1589 | copy of i1 = 1588 |
| 1590 | copy of c1 = 926 |
| 1591 | copy of c8 = 1586 |
| 1592 | copy of i1 = 1588 |
| 1593 | copy of i7 = 1557 |
| 1594 | copy of c9 = 1595 |
| 1595–1604 | constant blue |
| 1605 | copy of c7 = 1582 |
| 1606 | copy of c1 = 926 |
| 1607 | copy of c2 = 1573 |
| 1608 | copy of i5 = 1594 |
| 1609 | copy of c4 = 1479 |
| 1610 | copy of c9 = 1595 |
| 1611 | copy of c8 = 1586 |
| 1612 | copy of c6 = 1492 |
| 1613 | copy of c5 = 1483 |
| 1614 | copy of c7 = 1582 |
| 1615–1625 | constant red |
| 1626 | copy of i0 = 1061 |
| 1627 | copy of i1 = 1588 |
| 1628 | copy of i2 = 1576 |
| 1629 | copy of i3 = 1549 |
| 1630 | copy of i4 = 1554 |
| 1631 | copy of i6bar = 675 |
| 1632 | copy of i7 = 1557 |
| 1633 | copy of i9 = 1267 |
| 1634 | copy of i8 = 1079 |
| 1635 | copy of i2 = 1576 |
| 1636 | constant blue |
| 1637 | copy of c0 = 930 |
| 1638 | copy of i0 = 1061 |
| 1639 | copy of i3 = 1549 |
| 1640 | copy of c3 = 1338 |
| 1641 | copy of i0 = 1061 |
| 1642 | copy of c3 = 1338 |
| 1643 | copy of c4 = 1479 |
| 1644 | copy of c5 = 1483 |
| 1645 | copy of c6 = 1492 |
| 1646–1647 | copy of i6 = 1472 |
| 1648 | copy of i8 = 1079 |
| 1649 | copy of i6bar = 675 |
| 1650 | copy of i2 = 1576 |
| 1651 | copy of i9 = 1267 |
| 1652 | copy of c8 = 1586 |
| 1653 | copy of i6 = 1472 |
| 1654 | copy of i4 = 1554 |
| 1655 | copy of i8 = 1079 |
| 1656 | copy of c3 = 1338 |
| 1657 | copy of i5 = 1594 |
| 1658 | copy of c0 = 930 |
| 1659 | copy of c9 = 1595 |

| Type | Vertices |
|---|---|
| constant red | 11 |
| constant blue | 11 |
| c0 = 930 | 3 |
| c1 = 926 | 3 |
| c2 = 1573 | 3 |
| c3 = 1338 | 3 |
| c4 = 1479 | 3 |
| c5 = 1483 | 3 |
| c6 = 1492 | 3 |
| c7 = 1582 | 3 |
| c8 = 1586 | 3 |
| c9 = 1595 | 3 |
| i0 = 1061 | 3 |
| i1 = 1588 | 3 |
| i2 = 1576 | 3 |
| i3 = 1549 | 3 |
| i4 = 1554 | 3 |
| i5 = 1594 | 3 |
| i6 = 1472 | 4 |
| i7 = 1557 | 3 |
| i8 = 1079 | 3 |
| i9 = 1267 | 3 |
| i6bar = 675 | 2 |

In total there are 11 constant red, 11 constant blue and 63 copies.

r1212_1660.json records the same data in machine-readable form. verify/check_antipodal_projection.py and lean/gen/gen_data_1661.py read the types from the file itself, so they do not rely on these tables.
