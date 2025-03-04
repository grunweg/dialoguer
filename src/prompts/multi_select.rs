use std::{io, iter::repeat, ops::Rem};

use crate::{
    term::Term,
    theme::{self, SimpleTheme, TermThemeRenderer, Theme},
    Paging,
};

use crossterm::{
    event::{read, Event, KeyCode, KeyEvent},
    terminal,
};

/// Renders a multi select prompt.
///
/// ## Example usage
/// ```rust,no_run
/// # fn test() -> Result<(), Box<dyn std::error::Error>> {
/// use dialoguer::MultiSelect;
///
/// let items = vec!["Option 1", "Option 2"];
/// let chosen : Vec<usize> = MultiSelect::new()
///     .items(&items)
///     .interact()?;
/// # Ok(())
/// # }
/// ```
pub struct MultiSelect<'a> {
    defaults: Vec<bool>,
    items: Vec<String>,
    prompt: Option<String>,
    report: bool,
    clear: bool,
    max_length: Option<usize>,
    theme: &'a dyn Theme,
}

impl Default for MultiSelect<'static> {
    fn default() -> Self {
        Self::new()
    }
}

impl MultiSelect<'static> {
    /// Creates a multi select prompt.
    pub fn new() -> Self {
        Self::with_theme(&SimpleTheme)
    }
}

impl MultiSelect<'_> {
    /// Sets the clear behavior of the menu.
    ///
    /// The default is to clear the menu.
    pub fn clear(&mut self, val: bool) -> &mut Self {
        self.clear = val;
        self
    }

    /// Sets a defaults for the menu.
    pub fn defaults(&mut self, val: &[bool]) -> &mut Self {
        self.defaults = val
            .to_vec()
            .iter()
            .copied()
            .chain(repeat(false))
            .take(self.items.len())
            .collect();
        self
    }

    /// Sets an optional max length for a page
    ///
    /// Max length is disabled by None
    pub fn max_length(&mut self, val: usize) -> &mut Self {
        // Paging subtracts two from the capacity, paging does this to
        // make an offset for the page indicator. So to make sure that
        // we can show the intended amount of items we need to add two
        // to our value.
        self.max_length = Some(val + 2);
        self
    }

    /// Add a single item to the selector.
    #[inline]
    pub fn item<T: ToString>(&mut self, item: T) -> &mut Self {
        self.item_checked(item, false)
    }

    /// Add a single item to the selector with a default checked state.
    pub fn item_checked<T: ToString>(&mut self, item: T, checked: bool) -> &mut Self {
        self.items.push(item.to_string());
        self.defaults.push(checked);
        self
    }

    /// Adds multiple items to the selector.
    pub fn items<T: ToString>(&mut self, items: &[T]) -> &mut Self {
        for item in items {
            self.items.push(item.to_string());
            self.defaults.push(false);
        }
        self
    }

    /// Adds multiple items to the selector with checked state
    pub fn items_checked<T: ToString>(&mut self, items: &[(T, bool)]) -> &mut Self {
        for &(ref item, checked) in items {
            self.items.push(item.to_string());
            self.defaults.push(checked);
        }
        self
    }

    /// Prefaces the menu with a prompt.
    ///
    /// By default, when a prompt is set the system also prints out a confirmation after
    /// the selection. You can opt-out of this with [`report`](#method.report).
    pub fn with_prompt<S: Into<String>>(&mut self, prompt: S) -> &mut Self {
        self.prompt = Some(prompt.into());
        self
    }

    /// Indicates whether to report the selected values after interaction.
    ///
    /// The default is to report the selections.
    pub fn report(&mut self, val: bool) -> &mut Self {
        self.report = val;
        self
    }

    /// Enables user interaction and returns the result.
    ///
    /// The user can select the items with the 'Space' bar and on 'Enter' the indices of selected items will be returned.
    /// The dialog is rendered on stderr.
    /// Result contains `Vec<index>` if user hit 'Enter'.
    /// This unlike [`interact_opt`](Self::interact_opt) does not allow to quit with 'Esc' or 'q'.
    #[inline]
    pub fn interact(&self) -> io::Result<Vec<usize>> {
        self.interact_on(&Term::from_stderr())
    }

    /// Enables user interaction and returns the result.
    ///
    /// The user can select the items with the 'Space' bar and on 'Enter' the indices of selected items will be returned.
    /// The dialog is rendered on stderr.
    /// Result contains `Some(Vec<index>)` if user hit 'Enter' or `None` if user cancelled with 'Esc' or 'q'.
    #[inline]
    pub fn interact_opt(&self) -> io::Result<Option<Vec<usize>>> {
        self.interact_on_opt(&Term::from_stderr())
    }

    /// Like [interact](#method.interact) but allows a specific terminal to be set.
    ///
    /// ## Examples
    ///```rust,no_run
    /// use dialoguer::MultiSelect;
    /// use std::io;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let selections = MultiSelect::new()
    ///         .item("Option A")
    ///         .item("Option B")
    ///         .interact_on(&mut io::stderr())?;
    ///
    ///     println!("User selected options at indices {:?}", selections);
    ///
    ///     Ok(())
    /// }
    ///```
    #[inline]
    pub fn interact_on(&self, term: &Term) -> io::Result<Vec<usize>> {
        self._interact_on(term, false)?
            .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "Quit not allowed in this case"))
    }

    /// Like [`interact_opt`](Self::interact_opt) but allows a specific terminal to be set.
    ///
    /// ## Examples
    /// ```rust,no_run
    /// use dialoguer::MultiSelect;
    /// use std::io;
    ///
    /// fn main() -> std::io::Result<()> {
    ///     let selections = MultiSelect::new()
    ///         .item("Option A")
    ///         .item("Option B")
    ///         .interact_on_opt(&mut io::stdout())?;
    ///
    ///     match selections {
    ///         Some(positions) => println!("User selected options at indices {:?}", positions),
    ///         None => println!("User exited using Esc or q")
    ///     }
    ///
    ///     Ok(())
    /// }
    /// ```
    #[inline]
    pub fn interact_on_opt(&self, term: &Term) -> io::Result<Option<Vec<usize>>> {
        self._interact_on(term, true)
    }

    fn _interact_on(&self, term: &Term, allow_quit: bool) -> io::Result<Option<Vec<usize>>> {
        if self.items.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "Empty list of items given to `MultiSelect`",
            ));
        }

        let mut paging = Paging::new(term, self.items.len(), self.max_length);
        let mut render = TermThemeRenderer::new(term, self.theme);
        let mut sel = 0;

        let mut size_vec = Vec::new();

        for items in self
            .items
            .iter()
            .flat_map(|i| i.split('\n'))
            .collect::<Vec<_>>()
        {
            let size = &items.len();
            size_vec.push(*size);
        }

        let mut checked: Vec<bool> = self.defaults.clone();

        term.hide_cursor()?;

        loop {
            if let Some(ref prompt) = self.prompt {
                paging
                    .render_prompt(|paging_info| render.multi_select_prompt(prompt, paging_info))?;
            }

            for (idx, item) in self
                .items
                .iter()
                .enumerate()
                .skip(paging.current_page * paging.capacity)
                .take(paging.capacity)
            {
                render.multi_select_prompt_item(item, checked[idx], sel == idx)?;
            }

            term.flush()?;

            terminal::enable_raw_mode()?;
            if let Event::Key(KeyEvent { code, modifiers: _ }) = read().unwrap() {
                terminal::disable_raw_mode()?;
                match code {
                    KeyCode::Down | KeyCode::Tab | KeyCode::Char('j') => {
                        if sel == !0 {
                            sel = 0;
                        } else {
                            sel = (sel as u64 + 1).rem(self.items.len() as u64) as usize;
                        }
                    }
                    KeyCode::Up | KeyCode::BackTab | KeyCode::Char('k') => {
                        if sel == !0 {
                            sel = self.items.len() - 1;
                        } else {
                            sel = ((sel as i64 - 1 + self.items.len() as i64)
                                % (self.items.len() as i64))
                                as usize;
                        }
                    }
                    KeyCode::Left | KeyCode::Char('h') => {
                        if paging.active {
                            sel = paging.previous_page();
                        }
                    }
                    KeyCode::Right | KeyCode::Char('l') => {
                        if paging.active {
                            sel = paging.next_page();
                        }
                    }
                    KeyCode::Char(' ') => {
                        checked[sel] = !checked[sel];
                    }
                    KeyCode::Esc | KeyCode::Char('q') => {
                        if allow_quit {
                            if self.clear {
                                render.clear()?;
                            } else {
                                theme::clear_last_lines(&term, paging.capacity as u16)?;
                            }

                            term.show_cursor()?;
                            term.flush()?;

                            return Ok(None);
                        }
                    }
                    KeyCode::Enter => {
                        if self.clear {
                            render.clear()?;
                        }

                        if let Some(ref prompt) = self.prompt {
                            if self.report {
                                let selections: Vec<_> = checked
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(idx, &checked)| {
                                        if checked {
                                            Some(self.items[idx].as_str())
                                        } else {
                                            None
                                        }
                                    })
                                    .collect();

                                render.multi_select_prompt_selection(prompt, &selections[..])?;
                            }
                        }

                        term.show_cursor()?;
                        term.flush()?;

                        return Ok(Some(
                            checked
                                .into_iter()
                                .enumerate()
                                .filter_map(|(idx, checked)| if checked { Some(idx) } else { None })
                                .collect(),
                        ));
                    }
                    _ => {}
                }
            }
            paging.update(sel)?;

            if paging.active {
                render.clear()?;
            } else {
                render.clear_preserve_prompt(&size_vec)?;
            }
        }
    }
}

impl<'a> MultiSelect<'a> {
    /// Creates a multi select prompt with a specific theme.
    pub fn with_theme(theme: &'a dyn Theme) -> Self {
        Self {
            items: vec![],
            defaults: vec![],
            clear: true,
            prompt: None,
            report: true,
            max_length: None,
            theme,
        }
    }
}
