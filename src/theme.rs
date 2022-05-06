//! Customizes the rendering of the elements.
use std::{fmt, io};

use console::{style, Style, StyledObject, Term};

/// Implements a theme for dialoguer.
pub trait Theme {
    /// Format a prompt.
    #[inline]
    fn format_prompt(&self, f: &mut dyn fmt::Write, prompt: &str) -> fmt::Result {
        write!(f, "{}:", prompt)
    }

    /// Format out an error.
    #[inline]
    fn format_error(&self, f: &mut dyn fmt::Write, err: &str) -> fmt::Result {
        write!(f, "error: {}", err)
    }

    /// Format a confirmation prompt.
    ///
    /// `prompt` is the message of the confirmation prompt,
    /// `default` is the default choice for the prompt (if any).
    fn format_confirm_prompt(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        default: Option<bool>,
    ) -> fmt::Result {
        if !prompt.is_empty() {
            write!(f, "{} ", &prompt)?;
        }
        match default {
            None => write!(f, "[y/n] ")?,
            Some(true) => write!(f, "[Y/n] ")?,
            Some(false) => write!(f, "[y/N] ")?,
        }
        Ok(())
    }

    /// Format a confirmation prompt after selection.
    fn format_confirm_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        selection: Option<bool>,
    ) -> fmt::Result {
        let selection = selection.map(|b| if b { "yes" } else { "no" });

        match selection {
            Some(selection) if prompt.is_empty() => {
                write!(f, "{}", selection)
            }
            Some(selection) => {
                write!(f, "{} {}", &prompt, selection)
            }
            None if prompt.is_empty() => Ok(()),
            None => {
                write!(f, "{}", &prompt)
            }
        }
    }

    /// Format an input prompt.
    fn format_input_prompt(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        default: Option<&str>,
    ) -> fmt::Result {
        match default {
            Some(default) if prompt.is_empty() => write!(f, "[{}]: ", default),
            Some(default) => write!(f, "{} [{}]: ", prompt, default),
            None => write!(f, "{}: ", prompt),
        }
    }

    /// Format an input prompt after selection.
    #[inline]
    fn format_input_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        sel: &str,
    ) -> fmt::Result {
        write!(f, "{}: {}", prompt, sel)
    }

    /// Format a password prompt.
    #[inline]
    #[cfg(feature = "password")]
    fn format_password_prompt(&self, f: &mut dyn fmt::Write, prompt: &str) -> fmt::Result {
        self.format_input_prompt(f, prompt, None)
    }

    /// Format a password prompt after selection.
    #[inline]
    #[cfg(feature = "password")]
    fn format_password_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
    ) -> fmt::Result {
        self.format_input_prompt_selection(f, prompt, "[hidden]")
    }

    /// Format a selection prompt.
    #[inline]
    fn format_select_prompt(&self, f: &mut dyn fmt::Write, prompt: &str) -> fmt::Result {
        self.format_prompt(f, prompt)
    }

    /// Format a selection prompt after an item was selected.
    #[inline]
    fn format_select_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        sel: &str,
    ) -> fmt::Result {
        self.format_input_prompt_selection(f, prompt, sel)
    }

    /// Format a multi-selection prompt.
    #[inline]
    fn format_multi_select_prompt(&self, f: &mut dyn fmt::Write, prompt: &str) -> fmt::Result {
        self.format_prompt(f, prompt)
    }

    /// Format a sort prompt.
    #[inline]
    fn format_sort_prompt(&self, f: &mut dyn fmt::Write, prompt: &str) -> fmt::Result {
        self.format_prompt(f, prompt)
    }

    /// Format a multi-selection prompt after an item was selected.
    fn format_multi_select_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        selections: &[&str],
    ) -> fmt::Result {
        write!(f, "{}: ", prompt)?;
        for (idx, sel) in selections.iter().enumerate() {
            write!(f, "{}{}", if idx == 0 { "" } else { ", " }, sel)?;
        }
        Ok(())
    }

    /// Format a sort prompt after an item was selected.
    #[inline]
    fn format_sort_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        selections: &[&str],
    ) -> fmt::Result {
        self.format_multi_select_prompt_selection(f, prompt, selections)
    }

    /// Format a single selection prompt item.
    fn format_select_prompt_item(
        &self,
        f: &mut dyn fmt::Write,
        text: &str,
        active: bool,
    ) -> fmt::Result {
        write!(f, "{} {}", if active { ">" } else { " " }, text)
    }

    /// Format a single multi-selection prompt item.
    fn format_multi_select_prompt_item(
        &self,
        f: &mut dyn fmt::Write,
        text: &str,
        checked: bool,
        active: bool,
    ) -> fmt::Result {
        write!(
            f,
            "{} {}",
            match (checked, active) {
                (true, true) => "> [x]",
                (true, false) => "  [x]",
                (false, true) => "> [ ]",
                (false, false) => "  [ ]",
            },
            text
        )
    }

    /// Format a sort prompt item.
    fn format_sort_prompt_item(
        &self,
        f: &mut dyn fmt::Write,
        text: &str,
        picked: bool,
        active: bool,
    ) -> fmt::Result {
        write!(
            f,
            "{} {}",
            match (picked, active) {
                (true, true) => "> [x]",
                (false, true) => "> [ ]",
                (_, false) => "  [ ]",
            },
            text
        )
    }

    /// Format a fuzzy selection prompt.
    #[cfg(feature = "fuzzy-select")]
    fn format_fuzzy_select_prompt(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        search_term: &str,
        cursor_pos: usize,
    ) -> fmt::Result {
        if !prompt.is_empty() {
            write!(f, "{} ", prompt,)?;
        }

        if cursor_pos < search_term.len() {
            let st_head = search_term[0..cursor_pos].to_string();
            let st_tail = search_term[cursor_pos..search_term.len()].to_string();
            let st_cursor = "|".to_string();
            write!(f, "{}{}{}", st_head, st_cursor, st_tail)
        } else {
            let cursor = "|".to_string();
            write!(f, "{}{}", search_term.to_string(), cursor)
        }
    }
}

/// The default theme.
pub struct SimpleTheme;

impl Theme for SimpleTheme {}

/// A colorful theme
pub struct ColorfulTheme {
    /// The style for default values
    pub defaults_style: Style,
    /// The style for prompt
    pub prompt_style: Style,
    /// Prompt prefix value and style
    pub prompt_prefix: StyledObject<String>,
    /// Prompt suffix value and style
    pub prompt_suffix: StyledObject<String>,
    /// Prompt on success prefix value and style
    pub success_prefix: StyledObject<String>,
    /// Prompt on success suffix value and style
    pub success_suffix: StyledObject<String>,
    /// Error prefix value and style
    pub error_prefix: StyledObject<String>,
    /// The style for error message
    pub error_style: Style,
    /// The style for hints
    pub hint_style: Style,
    /// The style for values on prompt success
    pub values_style: Style,
    /// The style for active items
    pub active_item_style: Style,
    /// The style for inactive items
    pub inactive_item_style: Style,
    /// Active item in select prefix value and style
    pub active_item_prefix: StyledObject<String>,
    /// Inctive item in select prefix value and style
    pub inactive_item_prefix: StyledObject<String>,
    /// Checked item in multi select prefix value and style
    pub checked_item_prefix: StyledObject<String>,
    /// Unchecked item in multi select prefix value and style
    pub unchecked_item_prefix: StyledObject<String>,
    /// Picked item in sort prefix value and style
    pub picked_item_prefix: StyledObject<String>,
    /// Unpicked item in sort prefix value and style
    pub unpicked_item_prefix: StyledObject<String>,
    /// Formats the cursor for a fuzzy select prompt
    #[cfg(feature = "fuzzy-select")]
    pub fuzzy_cursor_style: Style,
    /// Show the selections from certain prompts inline
    pub inline_selections: bool,
}

impl Default for ColorfulTheme {
    fn default() -> ColorfulTheme {
        ColorfulTheme {
            defaults_style: Style::new().for_stderr().cyan(),
            prompt_style: Style::new().for_stderr().bold(),
            prompt_prefix: style("?".to_string()).for_stderr().yellow(),
            prompt_suffix: style("›".to_string()).for_stderr().black().bright(),
            success_prefix: style("✔".to_string()).for_stderr().green(),
            success_suffix: style("·".to_string()).for_stderr().black().bright(),
            error_prefix: style("✘".to_string()).for_stderr().red(),
            error_style: Style::new().for_stderr().red(),
            hint_style: Style::new().for_stderr().black().bright(),
            values_style: Style::new().for_stderr().green(),
            active_item_style: Style::new().for_stderr().cyan(),
            inactive_item_style: Style::new().for_stderr(),
            active_item_prefix: style("❯".to_string()).for_stderr().green(),
            inactive_item_prefix: style(" ".to_string()).for_stderr(),
            checked_item_prefix: style("✔".to_string()).for_stderr().green(),
            unchecked_item_prefix: style("✔".to_string()).for_stderr().black(),
            picked_item_prefix: style("❯".to_string()).for_stderr().green(),
            unpicked_item_prefix: style(" ".to_string()).for_stderr(),
            #[cfg(feature = "fuzzy-select")]
            fuzzy_cursor_style: Style::new().for_stderr().black().on_white(),
            inline_selections: true,
        }
    }
}

impl Theme for ColorfulTheme {
    /// Format a prompt.
    fn format_prompt(&self, f: &mut dyn fmt::Write, prompt: &str) -> fmt::Result {
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.prompt_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        write!(f, "{}", &self.prompt_suffix)
    }

    /// Format an error.
    fn format_error(&self, f: &mut dyn fmt::Write, err: &str) -> fmt::Result {
        write!(
            f,
            "{} {}",
            &self.error_prefix,
            self.error_style.apply_to(err)
        )
    }

    /// Format an input prompt.
    fn format_input_prompt(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        default: Option<&str>,
    ) -> fmt::Result {
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.prompt_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        match default {
            Some(default) => write!(
                f,
                "{} {} ",
                self.hint_style.apply_to(&format!("({})", default)),
                &self.prompt_suffix
            ),
            None => write!(f, "{} ", &self.prompt_suffix),
        }
    }

    /// Format a confirmation prompt.
    fn format_confirm_prompt(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        default: Option<bool>,
    ) -> fmt::Result {
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.prompt_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        match default {
            None => write!(
                f,
                "{} {}",
                self.hint_style.apply_to("(y/n)"),
                &self.prompt_suffix
            ),
            Some(true) => write!(
                f,
                "{} {} {}",
                self.hint_style.apply_to("(y/n)"),
                &self.prompt_suffix,
                self.defaults_style.apply_to("yes")
            ),
            Some(false) => write!(
                f,
                "{} {} {}",
                self.hint_style.apply_to("(y/n)"),
                &self.prompt_suffix,
                self.defaults_style.apply_to("no")
            ),
        }
    }

    /// Format a confirmation prompt after selection.
    fn format_confirm_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        selection: Option<bool>,
    ) -> fmt::Result {
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.success_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }
        let selection = selection.map(|b| if b { "yes" } else { "no" });

        match selection {
            Some(selection) => {
                write!(
                    f,
                    "{} {}",
                    &self.success_suffix,
                    self.values_style.apply_to(selection)
                )
            }
            None => {
                write!(f, "{}", &self.success_suffix)
            }
        }
    }

    /// Formats an input prompt after selection.
    fn format_input_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        sel: &str,
    ) -> fmt::Result {
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.success_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        write!(
            f,
            "{} {}",
            &self.success_suffix,
            self.values_style.apply_to(sel)
        )
    }

    /// Formats a password prompt after selection.
    #[cfg(feature = "password")]
    fn format_password_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
    ) -> fmt::Result {
        self.format_input_prompt_selection(f, prompt, "********")
    }

    /// Formats a multi select prompt after selection.
    fn format_multi_select_prompt_selection(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        selections: &[&str],
    ) -> fmt::Result {
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.success_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        write!(f, "{} ", &self.success_suffix)?;

        if self.inline_selections {
            for (idx, sel) in selections.iter().enumerate() {
                write!(
                    f,
                    "{}{}",
                    if idx == 0 { "" } else { ", " },
                    self.values_style.apply_to(sel)
                )?;
            }
        }

        Ok(())
    }

    /// Formats a select prompt item.
    fn format_select_prompt_item(
        &self,
        f: &mut dyn fmt::Write,
        text: &str,
        active: bool,
    ) -> fmt::Result {
        let details = if active {
            (
                &self.active_item_prefix,
                self.active_item_style.apply_to(text),
            )
        } else {
            (
                &self.inactive_item_prefix,
                self.inactive_item_style.apply_to(text),
            )
        };

        write!(f, "{} {}", details.0, details.1)
    }

    /// Formats a multi select prompt item.
    fn format_multi_select_prompt_item(
        &self,
        f: &mut dyn fmt::Write,
        text: &str,
        checked: bool,
        active: bool,
    ) -> fmt::Result {
        let details = match (checked, active) {
            (true, true) => (
                &self.checked_item_prefix,
                self.active_item_style.apply_to(text),
            ),
            (true, false) => (
                &self.checked_item_prefix,
                self.inactive_item_style.apply_to(text),
            ),
            (false, true) => (
                &self.unchecked_item_prefix,
                self.active_item_style.apply_to(text),
            ),
            (false, false) => (
                &self.unchecked_item_prefix,
                self.inactive_item_style.apply_to(text),
            ),
        };

        write!(f, "{} {}", details.0, details.1)
    }

    /// Formats a sort prompt item.
    fn format_sort_prompt_item(
        &self,
        f: &mut dyn fmt::Write,
        text: &str,
        picked: bool,
        active: bool,
    ) -> fmt::Result {
        let details = match (picked, active) {
            (true, true) => (
                &self.picked_item_prefix,
                self.active_item_style.apply_to(text),
            ),
            (false, true) => (
                &self.unpicked_item_prefix,
                self.active_item_style.apply_to(text),
            ),
            (_, false) => (
                &self.unpicked_item_prefix,
                self.inactive_item_style.apply_to(text),
            ),
        };

        write!(f, "{} {}", details.0, details.1)
    }

    /// Formats a fuzzy-selectprompt after selection.
    #[cfg(feature = "fuzzy-select")]
    fn format_fuzzy_select_prompt(
        &self,
        f: &mut dyn fmt::Write,
        prompt: &str,
        search_term: &str,
        cursor_pos: usize,
    ) -> fmt::Result {
        if !prompt.is_empty() {
            write!(
                f,
                "{} {} ",
                &self.prompt_prefix,
                self.prompt_style.apply_to(prompt)
            )?;
        }

        if cursor_pos < search_term.len() {
            let st_head = search_term[0..cursor_pos].to_string();
            let st_tail = search_term[cursor_pos + 1..search_term.len()].to_string();
            let st_cursor = self
                .fuzzy_cursor_style
                .apply_to(search_term.to_string().chars().nth(cursor_pos).unwrap());
            write!(
                f,
                "{} {}{}{}",
                &self.prompt_suffix, st_head, st_cursor, st_tail
            )
        } else {
            let cursor = self.fuzzy_cursor_style.apply_to(" ");
            write!(
                f,
                "{} {}{}",
                &self.prompt_suffix,
                search_term.to_string(),
                cursor
            )
        }
    }
}

/// Helper struct to conveniently render a theme to a term.
pub(crate) struct TermThemeRenderer<'a> {
    term: &'a Term,
    theme: &'a dyn Theme,
    /// Lengths of all output lines of the last completed prompt and everything above it.
    // We track this to handle overflowing lines when clearing the terminal.
    line_lengths_before_prompt: Vec<usize>,
    /// Lengths of all completed output lines after the last prompt:
    /// this does not include the current line.
    // We track this to handle overflowing lines when clearing the terminal.
    line_lengths_after_prompt: Vec<usize>,
    /// Length of the current line: `None` if we just completed a prompt.
    current_line_length: Option<usize>,
}

impl<'a> TermThemeRenderer<'a> {
    pub fn new(term: &'a Term, theme: &'a dyn Theme) -> TermThemeRenderer<'a> {
        TermThemeRenderer {
            term,
            theme,
            line_lengths_before_prompt: Vec::new(),
            line_lengths_after_prompt: Vec::new(),
            current_line_length: Some(0),
        }
    }

    #[cfg(feature = "password")]
    pub fn term(&self) -> &Term {
        self.term
    }

    /// Enlarge the theme by one line: allow displaying one more line of input.
    pub fn add_line(&mut self) {
        self.line_lengths_after_prompt.push(0);
    }

    /// Write a formatted string to this terminal. The string can be span multiple lines.
    ///
    /// `F` is a closure prescribing the text to write into the current instance.
    fn write_formatted_str<
        F: FnOnce(&mut TermThemeRenderer, &mut dyn fmt::Write) -> fmt::Result,
    >(
        &mut self,
        f: F,
    ) -> io::Result<()> {
        let mut buf = String::new();
        f(self, &mut buf).map_err(|err| io::Error::new(io::ErrorKind::Other, err))?;

        let mut line_lengths: Vec<_> = buf.lines().map(|l| l.len()).collect();
        assert_eq!(buf.chars().filter(|&x| x == '\n').count(), line_lengths.len() - 1); // sanity check of my logic

        // The first line of buf is printed on the current line.
        // The last line of buf becomes the new current line.
        line_lengths[0] += self.current_line_length.unwrap_or(0);
        self.current_line_length = Some(line_lengths.pop().unwrap());
        self.line_lengths_after_prompt.extend(line_lengths);

        self.term.write_str(&buf)
    }

    /// Like [`write_formatted_string`](#method::write_formatted_string), but add a linebreak afterwards.
    fn write_formatted_line<
        F: FnOnce(&mut TermThemeRenderer, &mut dyn fmt::Write) -> fmt::Result,
    >(
        &mut self,
        f: F,
    ) -> io::Result<()> {
        let mut buf = String::new();
        f(self, &mut buf).map_err(|err| io::Error::new(io::ErrorKind::Other, err))?;

        let mut line_lengths: Vec<_> = buf.lines().map(|l| l.len()).collect();
        assert_eq!(buf.chars().filter(|&x| x == '\n').count(), line_lengths.len() - 1); // sanity check of my logic

        // The first line of buf is printed on the current line.
        // We have an empty new line after the last line of buf.
        line_lengths[0] += self.current_line_length.unwrap_or(0);
        self.line_lengths_after_prompt.extend(line_lengths);
        self.current_line_length = Some(0);

        self.term.write_line(&buf)
    }

    /// Write a formatted prompt string to this terminal.
    ///
    /// `F` is a closure prescribing the text to write into the current instance.
    fn write_formatted_prompt<
        F: FnOnce(&mut TermThemeRenderer, &mut dyn fmt::Write) -> fmt::Result,
    >(
        &mut self,
        f: F,
    ) -> io::Result<()> {
        self.write_formatted_line(f)?;
        self.line_lengths_before_prompt.extend(self.line_lengths_after_prompt.iter());
        self.line_lengths_after_prompt.clear();
        self.current_line_length = None;
        Ok(())
    }

    fn write_paging_info(buf: &mut dyn fmt::Write, paging_info: (usize, usize)) -> fmt::Result {
        write!(buf, " [Page {}/{}] ", paging_info.0, paging_info.1)
    }

    pub fn error(&mut self, err: &str) -> io::Result<()> {
        self.write_formatted_line(|this, buf| this.theme.format_error(buf, err))
    }

    pub fn confirm_prompt(&mut self, prompt: &str, default: Option<bool>) -> io::Result<()> {
        self.write_formatted_str(|this, buf| this.theme.format_confirm_prompt(buf, prompt, default))
    }

    pub fn confirm_prompt_selection(&mut self, prompt: &str, sel: Option<bool>) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme.format_confirm_prompt_selection(buf, prompt, sel)
        })
    }

    #[cfg(feature = "fuzzy-select")]
    pub fn fuzzy_select_prompt(
        &mut self,
        prompt: &str,
        search_term: &str,
        cursor_pos: usize,
    ) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme
                .format_fuzzy_select_prompt(buf, prompt, search_term, cursor_pos)
        })
    }

    pub fn input_prompt(&mut self, prompt: &str, default: Option<&str>) -> io::Result<()> {
        self.write_formatted_str(|this, buf| this.theme.format_input_prompt(buf, prompt, default))
    }

    pub fn input_prompt_selection(&mut self, prompt: &str, sel: &str) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme.format_input_prompt_selection(buf, prompt, sel)
        })
    }

    #[cfg(feature = "password")]
    pub fn password_prompt(&mut self, prompt: &str) -> io::Result<()> {
        self.write_formatted_str(|this, buf| {
            write!(buf, "\r")?;
            this.theme.format_password_prompt(buf, prompt)
        })
    }

    #[cfg(feature = "password")]
    pub fn password_prompt_selection(&mut self, prompt: &str) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme.format_password_prompt_selection(buf, prompt)
        })
    }

    pub fn select_prompt(
        &mut self,
        prompt: &str,
        paging_info: Option<(usize, usize)>,
    ) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme.format_select_prompt(buf, prompt)?;

            if let Some(paging_info) = paging_info {
                TermThemeRenderer::write_paging_info(buf, paging_info)?;
            }

            Ok(())
        })
    }

    pub fn select_prompt_selection(&mut self, prompt: &str, sel: &str) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme.format_select_prompt_selection(buf, prompt, sel)
        })
    }

    pub fn select_prompt_item(&mut self, text: &str, active: bool) -> io::Result<()> {
        self.write_formatted_line(|this, buf| {
            this.theme.format_select_prompt_item(buf, text, active)
        })
    }

    pub fn multi_select_prompt(
        &mut self,
        prompt: &str,
        paging_info: Option<(usize, usize)>,
    ) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme.format_multi_select_prompt(buf, prompt)?;

            if let Some(paging_info) = paging_info {
                TermThemeRenderer::write_paging_info(buf, paging_info)?;
            }

            Ok(())
        })
    }

    pub fn multi_select_prompt_selection(&mut self, prompt: &str, sel: &[&str]) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme
                .format_multi_select_prompt_selection(buf, prompt, sel)
        })
    }

    pub fn multi_select_prompt_item(
        &mut self,
        text: &str,
        checked: bool,
        active: bool,
    ) -> io::Result<()> {
        self.write_formatted_line(|this, buf| {
            this.theme
                .format_multi_select_prompt_item(buf, text, checked, active)
        })
    }

    pub fn sort_prompt(
        &mut self,
        prompt: &str,
        paging_info: Option<(usize, usize)>,
    ) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme.format_sort_prompt(buf, prompt)?;

            if let Some(paging_info) = paging_info {
                TermThemeRenderer::write_paging_info(buf, paging_info)?;
            }

            Ok(())
        })
    }

    pub fn sort_prompt_selection(&mut self, prompt: &str, sel: &[&str]) -> io::Result<()> {
        self.write_formatted_prompt(|this, buf| {
            this.theme.format_sort_prompt_selection(buf, prompt, sel)
        })
    }

    pub fn sort_prompt_item(&mut self, text: &str, picked: bool, active: bool) -> io::Result<()> {
        self.write_formatted_line(|this, buf| {
            this.theme
                .format_sort_prompt_item(buf, text, picked, active)
        })
    }

    /// Clear the current theme.
    ///
    /// Position the cursor at the beginning of the current line.
    pub fn clear(&mut self) -> io::Result<()> {
        // Account for lines overflowing the current terminal width.
        let mut overflowed_height = 0;
        for size in self.line_lengths_before_prompt.iter().chain(self.line_lengths_after_prompt.iter()) {
            let term_width = self.term.size().1 as usize;
            overflowed_height += *size / term_width;
        }
        // clear the current line first, so the cursor ends at the beginning of the current line.
        self.term.clear_line()?;
        let height = self.line_lengths_before_prompt.len();
        let prompt_height= self.line_lengths_after_prompt.len();
        self.term
            .clear_last_lines(height + prompt_height + overflowed_height)?;
        // self.term now contains height + prompt_height empty lines after
        // the current line. That doesn't really matter, as these are empty.
        self.line_lengths_before_prompt.clear();
        self.line_lengths_after_prompt.clear();
        self.current_line_length = Some(0);
        Ok(())
    }

    /// Clear all output after the last completed prompt; leave the prompt behind.
    pub fn clear_preserve_prompt(&mut self) -> io::Result<()> {
        // Account for lines overflowing the current terminal width.
        let mut extra_height = 0;
        for size in self.line_lengths_after_prompt.iter() {
            let term_width = self.term.size().1 as usize;
            extra_height += size / term_width;
        }
        self.term.clear_line()?;
        self.term.clear_last_lines(self.line_lengths_after_prompt.len() + extra_height)?;
        self.line_lengths_after_prompt.clear();
        self.current_line_length = Some(0);
        Ok(())
    }
}
