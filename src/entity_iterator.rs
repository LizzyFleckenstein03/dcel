use crate::*;

/// An iterator over a linked list of entities.
///
/// See the various `.iter_*()` methods on [`Ptr`] for details.
pub struct EntityIterator<'tok, 'brand, 'arena, T>(Option<(lens_t!(T), lens_t!(T))>);

impl<'tok, 'brand, 'arena, T> Clone for EntityIterator<'tok, 'brand, 'arena, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'tok, 'brand, 'arena, T> Copy for EntityIterator<'tok, 'brand, 'arena, T> {}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> EntityIterator<'tok, 'brand, 'arena, T> {
    pub(crate) fn new(
        start: Option<ptr_t!(T)>,
        token: &'tok impl ReflAsRef<GhostToken<'brand>>,
    ) -> Self {
        Self(start.map(|s| {
            let l = Lens::new(s, token);
            (l, l.prev())
        }))
    }
}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> Iterator
    for EntityIterator<'tok, 'brand, 'arena, T>
{
    type Item = lens_t!(T);

    fn next(&mut self) -> Option<Self::Item> {
        let range = self.0.as_mut()?;
        let ret = range.0;

        if range.0 == range.1 {
            self.0 = None;
        } else {
            range.0 = range.0.next();
        }

        Some(ret)
    }
}

impl<'tok, 'brand, 'arena, T: Entity<'brand, 'arena>> DoubleEndedIterator
    for EntityIterator<'tok, 'brand, 'arena, T>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let range = self.0.as_mut()?;
        let ret = range.1;

        if range.0 == range.1 {
            self.0 = None;
        } else {
            range.1 = range.1.prev();
        }

        Some(ret)
    }
}
