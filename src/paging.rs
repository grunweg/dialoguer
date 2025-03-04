use std::io;

use crossterm::terminal;

use crate::{term::Term, theme, DEFAULT_TERMINAL_SIZE};

/// Creates a paging module
///
/// The paging module serves as tracking structure to allow paged views
/// and automatically (de-)activates paging depending on the current terminal size.
pub struct Paging<'a> {
    pub pages: usize,
    pub current_page: usize,
    pub capacity: usize,
    pub active: bool,
    pub max_capacity: Option<usize>,
    term: &'a Term,
    current_term_size: (u16, u16),
    items_len: usize,
    activity_transition: bool,
}

impl<'a> Paging<'a> {
    pub fn new(term: &Term, items_len: usize, max_capacity: Option<usize>) -> Paging {
        let term_size = terminal::size().unwrap_or(DEFAULT_TERMINAL_SIZE);
        // Subtract -2 because we need space to render the prompt, if paging is active
        let capacity = max_capacity
            .unwrap_or(std::usize::MAX)
            .min(term_size.0 as usize)
            // Safeguard in case term_size or max_length is 2 or less. Guarantees no unwanted wrapping behavior.
            .max(3)
            - 2;
        let pages = (items_len as f64 / capacity as f64).ceil() as usize;

        Paging {
            pages,
            current_page: 0,
            capacity,
            active: pages > 1,
            term,
            current_term_size: term_size,
            items_len,
            max_capacity,
            // Set transition initially to true to trigger prompt rendering for inactive paging on start
            activity_transition: true,
        }
    }

    /// Updates all internal based on the current terminal size and cursor position
    pub fn update(&mut self, cursor_pos: usize) -> io::Result<()> {
        let new_term_size = terminal::size().unwrap_or(DEFAULT_TERMINAL_SIZE);

        if self.current_term_size != new_term_size {
            self.current_term_size = new_term_size;
            self.capacity = self
                .max_capacity
                .unwrap_or(std::usize::MAX)
                .min(self.current_term_size.0 as usize)
                .max(3)
                - 2;
            self.pages = (self.items_len as f64 / self.capacity as f64).ceil() as usize;
        }

        if self.active == (self.pages > 1) {
            self.activity_transition = false;
        } else {
            self.active = self.pages > 1;
            self.activity_transition = true;
            // Clear everything to prevent "ghost" lines in terminal when a resize happened.
            theme::clear_last_lines(&self.term, self.capacity as u16)?;
        }

        if cursor_pos != !0
            && (cursor_pos < self.current_page * self.capacity
                || cursor_pos >= (self.current_page + 1) * self.capacity)
        {
            self.current_page = cursor_pos / self.capacity;
        }

        Ok(())
    }

    /// Renders a prompt when the following conditions are met:
    /// * Paging is active
    /// * Transition of the paging activity happened (active -> inactive / inactive -> active)
    pub fn render_prompt<F>(&mut self, mut render_prompt: F) -> io::Result<()>
    where
        F: FnMut(Option<(usize, usize)>) -> io::Result<()>,
    {
        if self.active {
            let paging_info = Some((self.current_page + 1, self.pages));
            render_prompt(paging_info)?;
        } else if self.activity_transition {
            render_prompt(None)?;
        }

        self.term.flush()?;

        Ok(())
    }

    /// Navigates to the next page
    pub fn next_page(&mut self) -> usize {
        if self.current_page == self.pages - 1 {
            self.current_page = 0;
        } else {
            self.current_page += 1;
        }

        self.current_page * self.capacity
    }

    /// Navigates to the previous page
    pub fn previous_page(&mut self) -> usize {
        if self.current_page == 0 {
            self.current_page = self.pages - 1;
        } else {
            self.current_page -= 1;
        }

        self.current_page * self.capacity
    }
}
