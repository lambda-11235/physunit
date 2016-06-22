
# PhysUnit

PhysUnit is a dimensional analysis library for Idris. It is very simple, only
supporting SI units without a special notation for prefixes. Here's an example
of its usage

``` idris
import PhysUnit

length : Quantity Double Meter
length = 5.9 =| Meter

-- DQuantity = Quantity Double
mass : DQuantity Kilogram
mass = 4.5 =| Kilogram

time : DQuantity Second
time = 5.43e-6 =| Second

force : DQuantity Newton
force = length :* mass :/ (time :^ 2)

area : DQuantity (Meter ^: 2)
area = (5.4 =| Meter) :* (9.8 =| Meter)

length2 : DQuantity Meter
length2 = sqrtQ area
```

Note that quantities are constructed with =|, quantity operators begin with :,
and unit operators end with :.

**This library is experimental and may be subject to API breaking changes.**
