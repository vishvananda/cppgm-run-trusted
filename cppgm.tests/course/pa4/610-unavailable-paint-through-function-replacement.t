#define F(x) G ## x
#define G0 F(0)
G0

#undef F
#undef G0

#define F() G ## 0
#define G0 F()
G0

#undef F
#undef G0

#define F() G0
#define G0 F()
G0
