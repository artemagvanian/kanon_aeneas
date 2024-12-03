#![feature(register_tool)]
#![register_tool(aeneas)]

#[derive(Clone)]
pub struct Record {
    pub age: u32,
    pub zip: u32,
    pub salary: u32,
}

impl Record {
    pub fn is_similar(&self, other: &Self) -> bool {
        self.age == other.age && self.zip == other.zip
    }
}

pub struct KAnonymity {
    data: Vec<Record>,
    k: usize,
}

impl KAnonymity {
    pub fn new(data: Vec<Record>, k: usize) -> Self {
        KAnonymity { data, k }
    }

    pub fn count_similar_rows(&self, row: &Record) -> usize {
        let mut n_similar = 0;
        let mut i = 0;
        while i < self.data.len() {
            if row.is_similar(&self.data[i]) {
                n_similar += 1;
            };
            i += 1;
        }
        n_similar
    }

    pub fn anonymize(&self) -> Vec<Record> {
        let mut anonymized_data = Vec::new();
        let mut i = 0;
        while i < self.data.len() {
            let row = self.data[i].clone();
            if self.count_similar_rows(&row) >= self.k {
                anonymized_data.push(row);
            }
            i += 1;
        }
        anonymized_data
    }
}
