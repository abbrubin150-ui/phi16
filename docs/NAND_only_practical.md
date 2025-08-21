# NAND-only בפועל — מדריך יישום הנדסי

מטרה: תרגול הדרישה NAND-only להנחיות פרקטיות בחומרה ובתוכנה.

1) חומרה / IR
צנרת סינתזה: קומפילציה ל-IR מבוסס NAND בלבד; לינט שדוחה OR/XOR/AND ישירים.

שקילות פורמלית: RTL ↔ Netlist-NAND (EC), כיסוי 100%.

דוגמה (Verilog-IR תיאורטי):

```verilog
// Original
assign out = a | b;

// NAND-only IR
wire not_a, not_b;
nand_gate n1(not_a, a, a);
nand_gate n2(not_b, b, b);
nand_gate n3(out, not_a, not_b);
```

2) תוכנה
ספריות סטנדרטיות: כל בוליאני נבנה מ-nand() פרימיטיבי.

בדיקות סטטיות (CI): לינט שחוסם || && ^ וכד'.

```python
def nand(a: bool, b: bool) -> bool:
    return not (a and b)

def logical_not(a: bool) -> bool:
    return nand(a, a)

def logical_or(a: bool, b: bool) -> bool:
    return nand(logical_not(a), logical_not(b))
```

3) תזמון וערוצי-צד
Propagation Delay: עומק לוגי גדל → ניתוח STA ושמירת מרווחי δ (QTPU).

Side-Channels: שונות בעומק נתיבים → נרמול בזמני ביצוע/הספק (dummy ops, shaping).

מסמכים קשורים: spec/ir/nand_ir_semantics.md, NAND_only_policy.yaml.
