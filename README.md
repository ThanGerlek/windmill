# Windmill

## Problem statement

Let S be a set of at least two points in the plane. Assume that no three points are collinear.
A windmill is a process that starts with a line l going through a single point P ∈ S.
The line rotates clockwise about a pivot P until the first time that the line meets some
other point belonging to S. This point, Q, takes over as the new pivot,
and the line now rotates clockwise about Q, until it next meets a point of S.
This process continues indefinitely.

Show that we can choose a point P in S and a line l going through P
such that the resulting windmill uses each point of S as a pivot infinitely many times.

## WIP Proof outline

NL Proof:
1. Define the problem.
2. Define the invariant.
     Define "on the right" of the line (the pivot is not).
     Invariant: number of points "on the right" (when in-between pivots)
3. Prove that it is invariant.
     When the line hits a pivot, the new pivot moves from one side to center,
     and the old pivot moves from center to that same side. So the number of points
     on that side doesn't change.
     - Show that the old pivot will gain the OTR-ness that the new pivot had.

4. Show that we can set the invariant to any value (less than N) by choosing the starting line.
5. Show that if the invariant is (N-1)/2, we must get back to start after 180.
     It must be parallel (call it vertical), and the pivot must be the same
     point it started on (because a vertical line through any other point would not have
     the cross-invariant equal to the invariant (+-1)).
     So it's the same starting line.
     1. Show that the number of non-OTR points equals the number of OTR points.

6. Show that, after 180, we have passed through every point as a pivot.

7. Show that this is sufficient.
   - "A 360 rotation back to start" is NOT sufficient.

-- Guys: light blue or light purple tie, dark pants.
-- Girls: light blue or light purple (solid or floral).
-- Get an airbnb in Utah...?
