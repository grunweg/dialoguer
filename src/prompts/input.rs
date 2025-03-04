use std::{fmt::Debug, io, iter, str::FromStr};

#[cfg(feature = "completion")]
use crate::completion::Completion;
#[cfg(feature = "history")]
use crate::history::History;
use crate::{
    term::Term,
    theme::{SimpleTheme, TermThemeRenderer, Theme},
    validate::Validator,
};

use crossterm::{
    event::{read, Event, KeyCode, KeyEvent},
    terminal,
    tty::IsTty,
};

/// Renders an input prompt.
///
/// ## Example usage
///
/// ```rust,no_run
/// use dialoguer::Input;
///
/// # fn test() -> Result<(), Box<dyn std::error::Error>> {
/// let input : String = Input::new()
///     .with_prompt("Tea or coffee?")
///     .with_initial_text("Yes")
///     .default("No".into())
///     .interact_text()?;
/// # Ok(())
/// # }
/// ```
/// It can also be used with turbofish notation:
///
/// ```rust,no_run
/// # fn test() -> Result<(), Box<dyn std::error::Error>> {
/// # use dialoguer::Input;
/// let input = Input::<String>::new()
///     .interact_text()?;
/// # Ok(())
/// # }
/// ```
pub struct Input<'a, T> {
    prompt: String,
    report: bool,
    default: Option<T>,
    show_default: bool,
    initial_text: Option<String>,
    theme: &'a dyn Theme,
    permit_empty: bool,
    validator: Option<Box<dyn FnMut(&T) -> Option<String> + 'a>>,
    #[cfg(feature = "history")]
    history: Option<&'a mut dyn History<T>>,
    #[cfg(feature = "completion")]
    completion: Option<&'a dyn Completion>,
}

impl<T> Default for Input<'static, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Input<'_, T> {
    /// Creates an input prompt.
    pub fn new() -> Self {
        Self::with_theme(&SimpleTheme)
    }

    /// Sets the input prompt.
    pub fn with_prompt<S: Into<String>>(&mut self, prompt: S) -> &mut Self {
        self.prompt = prompt.into();
        self
    }

    /// Indicates whether to report the input value after interaction.
    ///
    /// The default is to report the input value.
    pub fn report(&mut self, val: bool) -> &mut Self {
        self.report = val;
        self
    }

    /// Sets initial text that user can accept or erase.
    pub fn with_initial_text<S: Into<String>>(&mut self, val: S) -> &mut Self {
        self.initial_text = Some(val.into());
        self
    }

    /// Sets a default.
    ///
    /// Out of the box the prompt does not have a default and will continue
    /// to display until the user inputs something and hits enter. If a default is set the user
    /// can instead accept the default with enter.
    pub fn default(&mut self, value: T) -> &mut Self {
        self.default = Some(value);
        self
    }

    /// Enables or disables an empty input
    ///
    /// By default, if there is no default value set for the input, the user must input a non-empty string.
    pub fn allow_empty(&mut self, val: bool) -> &mut Self {
        self.permit_empty = val;
        self
    }

    /// Disables or enables the default value display.
    ///
    /// The default behaviour is to append [`default`](#method.default) to the prompt to tell the
    /// user what is the default value.
    ///
    /// This method does not affect existence of default value, only its display in the prompt!
    pub fn show_default(&mut self, val: bool) -> &mut Self {
        self.show_default = val;
        self
    }
}

impl<'a, T> Input<'a, T> {
    /// Creates an input prompt with a specific theme.
    pub fn with_theme(theme: &'a dyn Theme) -> Self {
        Self {
            prompt: "".into(),
            report: true,
            default: None,
            show_default: true,
            initial_text: None,
            theme,
            permit_empty: false,
            validator: None,
            #[cfg(feature = "history")]
            history: None,
            #[cfg(feature = "completion")]
            completion: None,
        }
    }

    /// Enable history processing
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use dialoguer::{History, Input};
    /// # use std::{collections::VecDeque, fmt::Display};
    /// let mut history = MyHistory::default();
    /// loop {
    ///     if let Ok(input) = Input::<String>::new()
    ///         .with_prompt("hist")
    ///         .history_with(&mut history)
    ///         .interact_text()
    ///     {
    ///         // Do something with the input
    ///     }
    /// }
    /// # struct MyHistory {
    /// #     history: VecDeque<String>,
    /// # }
    /// #
    /// # impl Default for MyHistory {
    /// #     fn default() -> Self {
    /// #         MyHistory {
    /// #             history: VecDeque::new(),
    /// #         }
    /// #     }
    /// # }
    /// #
    /// # impl<T: ToString> History<T> for MyHistory {
    /// #     fn read(&self, pos: usize) -> Option<String> {
    /// #         self.history.get(pos).cloned()
    /// #     }
    /// #
    /// #     fn write(&mut self, val: &T)
    /// #     where
    /// #     {
    /// #         self.history.push_front(val.to_string());
    /// #     }
    /// # }
    /// ```
    #[cfg(feature = "history")]
    pub fn history_with<H>(&mut self, history: &'a mut H) -> &mut Self
    where
        H: History<T>,
    {
        self.history = Some(history);
        self
    }

    /// Enable completion
    #[cfg(feature = "completion")]
    pub fn completion_with<C>(&mut self, completion: &'a C) -> &mut Self
    where
        C: Completion,
    {
        self.completion = Some(completion);
        self
    }
}

impl<'a, T> Input<'a, T>
where
    T: 'a,
{
    /// Registers a validator.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # use dialoguer::Input;
    /// let mail: String = Input::new()
    ///     .with_prompt("Enter email")
    ///     .validate_with(|input: &String| -> Result<(), &str> {
    ///         if input.contains('@') {
    ///             Ok(())
    ///         } else {
    ///             Err("This is not a mail address")
    ///         }
    ///     })
    ///     .interact()
    ///     .unwrap();
    /// ```
    pub fn validate_with<V>(&mut self, mut validator: V) -> &mut Self
    where
        V: Validator<T> + 'a,
        V::Err: ToString,
    {
        let mut old_validator_func = self.validator.take();

        self.validator = Some(Box::new(move |value: &T| -> Option<String> {
            if let Some(old) = old_validator_func.as_mut() {
                if let Some(err) = old(value) {
                    return Some(err);
                }
            }

            match validator.validate(value) {
                Ok(()) => None,
                Err(err) => Some(err.to_string()),
            }
        }));

        self
    }
}

impl<T> Input<'_, T>
where
    T: Clone + ToString + FromStr,
    <T as FromStr>::Err: Debug + ToString,
{
    /// Enables the user to enter a printable ascii sequence and returns the result.
    ///
    /// Its difference from [`interact`](#method.interact) is that it only allows ascii characters for string,
    /// while [`interact`](#method.interact) allows virtually any character to be used e.g arrow keys.
    ///
    /// The dialog is rendered on stderr.
    pub fn interact_text(&mut self) -> io::Result<T> {
        self.interact_text_on(&Term::from_stderr())
    }

    /// Like [`interact_text`](#method.interact_text) but allows a specific terminal to be set.
    pub fn interact_text_on(&mut self, term: &Term) -> io::Result<T> {
        let mut render = TermThemeRenderer::new(term, self.theme);

        loop {
            let default_string = self.default.as_ref().map(ToString::to_string);

            render.input_prompt(
                &self.prompt,
                if self.show_default {
                    default_string.as_deref()
                } else {
                    None
                },
            )?;
            term.flush()?;

            // Read input by keystroke so that we can suppress ascii control characters.
            if !io::stdout().is_tty() {
                return Ok("".to_owned().parse::<T>().unwrap());
            }

            let mut chars: Vec<char> = Vec::new();
            let mut position = 0;
            #[cfg(feature = "history")]
            let mut hist_pos = 0;

            if let Some(initial) = self.initial_text.as_ref() {
                render.write_str(initial)?;
                chars = initial.chars().collect();
                position = chars.len();
            }

            loop {
                terminal::enable_raw_mode()?;
                if let Event::Key(KeyEvent { code, modifiers: _ }) = read().unwrap() {
                    terminal::disable_raw_mode()?;
                    match code {
                        KeyCode::Backspace if position > 0 => {
                            position -= 1;
                            chars.remove(position);
                            render.clear_last_chars(1)?;

                            let tail: String = chars[position..].iter().collect();

                            if !tail.is_empty() {
                                render.write_str(&tail)?;
                                render.move_cursor_left(tail.len() as u16)?;
                            }

                            term.flush()?;
                        }
                        KeyCode::Char(chr) if !chr.is_ascii_control() => {
                            chars.insert(position, chr);
                            position += 1;
                            let tail: String =
                                iter::once(&chr).chain(chars[position..].iter()).collect();
                            render.write_str(&tail)?;
                            render.move_cursor_left((tail.len() - 1) as u16)?;
                            term.flush()?;
                        }
                        KeyCode::Left if position > 0 => {
                            render.move_cursor_left(1)?;
                            position -= 1;
                            term.flush()?;
                        }
                        KeyCode::Right if position < chars.len() => {
                            render.move_cursor_right(1)?;
                            position += 1;
                            term.flush()?;
                        }
                        #[cfg(feature = "completion")]
                        KeyCode::Right | KeyCode::Tab => {
                            if let Some(completion) = &self.completion {
                                let input: String = chars.clone().into_iter().collect();
                                if let Some(x) = completion.get(&input) {
                                    render.clear_last_chars(chars.len() as u16)?;
                                    chars.clear();
                                    position = 0;
                                    for ch in x.chars() {
                                        chars.insert(position, ch);
                                        position += 1;
                                    }
                                    render.write_str(&x)?;
                                    term.flush()?;
                                }
                            }
                        }
                        #[cfg(feature = "history")]
                        KeyCode::Up => {
                            if let Some(history) = &self.history {
                                if let Some(previous) = history.read(hist_pos) {
                                    hist_pos += 1;
                                    render.clear_last_chars(chars.len() as u16)?;
                                    chars.clear();
                                    position = 0;
                                    for ch in previous.chars() {
                                        chars.insert(position, ch);
                                        position += 1;
                                    }
                                    render.write_str(&previous)?;
                                    term.flush()?;
                                }
                            }
                        }
                        #[cfg(feature = "history")]
                        KeyCode::Down => {
                            if let Some(history) = &self.history {
                                // Move the history position back one in case we have up arrowed into it
                                // and the position is sitting on the next to read
                                if let Some(pos) = hist_pos.checked_sub(1) {
                                    hist_pos = pos;
                                    // Move it back again to get the previous history entry
                                    if let Some(pos) = pos.checked_sub(1) {
                                        if let Some(previous) = history.read(pos) {
                                            render.clear_last_chars(chars.len() as u16)?;
                                            chars.clear();
                                            position = 0;
                                            for ch in previous.chars() {
                                                chars.insert(position, ch);
                                                position += 1;
                                            }
                                            render.write_str(&previous)?;
                                            term.flush()?;
                                        }
                                    } else {
                                        render.clear_last_chars(chars.len() as u16)?;
                                        chars.clear();
                                        position = 0;
                                    }
                                } else {
                                    render.clear_last_chars(chars.len() as u16)?;
                                    chars.clear();
                                    position = 0;
                                }
                            }
                        }
                        KeyCode::Enter => break,
                        KeyCode::Null => {
                            return Err(io::Error::new(
                                io::ErrorKind::NotConnected,
                                "Not a terminal",
                            ))
                        }
                        _ => (),
                    }
                }
            }
            let input = chars.iter().collect::<String>();

            render.clear()?;

            if chars.is_empty() {
                if let Some(ref default) = self.default {
                    if let Some(ref mut validator) = self.validator {
                        if let Some(err) = validator(default) {
                            render.error(&err)?;
                            continue;
                        }
                    }

                    if self.report {
                        render.input_prompt_selection(&self.prompt, &default.to_string())?;
                    }
                    term.flush()?;
                    return Ok(default.clone());
                } else if !self.permit_empty {
                    continue;
                }
            }

            match input.parse::<T>() {
                Ok(value) => {
                    if let Some(ref mut validator) = self.validator {
                        if let Some(err) = validator(&value) {
                            render.error(&err)?;
                            continue;
                        }
                    }

                    #[cfg(feature = "history")]
                    if let Some(history) = &mut self.history {
                        history.write(&value);
                    }

                    if self.report {
                        render.input_prompt_selection(&self.prompt, &input)?;
                    }
                    term.flush()?;

                    return Ok(value);
                }
                Err(err) => {
                    render.error(&err.to_string())?;
                    continue;
                }
            }
        }
    }
}

impl<T> Input<'_, T>
where
    T: Clone + ToString + FromStr,
    <T as FromStr>::Err: ToString,
{
    /// Enables user interaction and returns the result.
    ///
    /// Allows any characters as input, including e.g arrow keys.
    /// Some of the keys might have undesired behavior.
    /// For more limited version, see [`interact_text`](#method.interact_text).
    ///
    /// If the user confirms the result is `true`, `false` otherwise.
    /// The dialog is rendered on stderr.
    pub fn interact(&mut self) -> io::Result<T> {
        self.interact_on(&Term::from_stderr())
    }

    /// Like [`interact`](#method.interact) but allows a specific terminal to be set.
    pub fn interact_on(&mut self, term: &Term) -> io::Result<T> {
        let mut render = TermThemeRenderer::new(term, self.theme);

        loop {
            let default_string = self.default.as_ref().map(ToString::to_string);

            render.input_prompt(
                &self.prompt,
                if self.show_default {
                    default_string.as_deref()
                } else {
                    None
                },
            )?;
            term.flush()?;

            let mut chars = if let Some(initial_text) = self.initial_text.as_ref() {
                render.write_str(initial_text)?;
                initial_text.chars().collect()
            } else {
                Vec::new()
            };
            loop {
                terminal::enable_raw_mode()?;
                if let Event::Key(KeyEvent { code, modifiers: _ }) = read().unwrap() {
                    terminal::disable_raw_mode()?;
                    match code {
                        KeyCode::Backspace => {
                            if chars.pop().is_some() {
                                render.clear_last_chars(1)?;
                            }
                            term.flush()?;
                        }
                        KeyCode::Char(chr) => {
                            chars.push(chr);
                            render.write_str(&chr.to_string())?;
                            term.flush()?;
                        }
                        KeyCode::Enter => {
                            render.write_str("\n")?;
                            break;
                        }
                        KeyCode::Null => {
                            return Err(io::Error::new(
                                io::ErrorKind::NotConnected,
                                "Not a terminal",
                            ))
                        }
                        _ => (),
                    }
                }
            }
            let input = chars.iter().collect::<String>();

            render.add_line();
            render.clear()?;

            if input.is_empty() {
                if let Some(ref default) = self.default {
                    if let Some(ref mut validator) = self.validator {
                        if let Some(err) = validator(default) {
                            render.error(&err)?;
                            continue;
                        }
                    }

                    if self.report {
                        render.input_prompt_selection(&self.prompt, &default.to_string())?;
                    }
                    term.flush()?;
                    return Ok(default.clone());
                } else if !self.permit_empty {
                    continue;
                }
            }

            match input.parse::<T>() {
                Ok(value) => {
                    if let Some(ref mut validator) = self.validator {
                        if let Some(err) = validator(&value) {
                            render.error(&err)?;
                            continue;
                        }
                    }

                    if self.report {
                        render.input_prompt_selection(&self.prompt, &input)?;
                    }
                    term.flush()?;

                    return Ok(value);
                }
                Err(err) => {
                    render.error(&err.to_string())?;
                    continue;
                }
            }
        }
    }
}
