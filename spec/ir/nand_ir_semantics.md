# NAND-IR — סמנטיקה אופרציונלית

תחביר: \( e ::= x \mid \mathrm{nand}(e_1,e_2) \).

סמנטיקה: \( \langle e,\sigma \rangle \Downarrow v \) — חישוב ערך בהינתן סביבה \( \sigma \).

- **VAR:** \( \frac{} {\langle x,\sigma \rangle \Downarrow \sigma(x)} \)
- **NAND:** \( \frac{\langle e_1,\sigma \rangle \Downarrow v_1 \quad \langle e_2,\sigma \rangle \Downarrow v_2}
             {\langle \mathrm{nand}(e_1,e_2),\sigma \rangle \Downarrow \neg(v_1 \land v_2)} \)

נגזרות תקינות:
- **NOT:** \( \mathrm{not}(e) := \mathrm{nand}(e,e) \)
- **AND:** \( \mathrm{and}(e_1,e_2) := \mathrm{not}(\mathrm{nand}(e_1,e_2)) \)
- **OR:** \( \mathrm{or}(e_1,e_2) := \mathrm{nand}(\mathrm{not}(e_1),\mathrm{not}(e_2)) \)
